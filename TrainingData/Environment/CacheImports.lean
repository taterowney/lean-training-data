import Lean
import Lean.Environment
import TrainingData.Environment.CacheImportsInitializer

open Lean System Std.Time

public section

open private ImportedModule ImportedModule.parts ImportedModule.irData? ImportedModule.needsData ImportedModule.needsIRTrans ImportedModule.mk
ImportState.mk ImportState.moduleNameMap ImportState.moduleNames Lean.ImportedModule.mainModule?
from Lean.Environment

open private importingRef runInitializersRef from Lean.ImportingFlag



/-- Find the compiled `.olean` of a module in the `LEAN_PATH` search path. Caches results. -/
partial def findOLean' (mod : Name) : ImportStateM FilePath := do
  match (← oleanPathCache.get).get? mod with
  | some fname => return fname
  | none => do
  let sp ← searchPathRef.get
  if let some fname ← sp.findWithExt "olean" mod then
    return fname
  else
    let pkg := FilePath.mk <| mod.getRoot.toString (escape := false)
    throw <| IO.userError s!"unknown module prefix '{pkg}'\n\n\
      No directory '{pkg}' or file '{pkg}.olean' in the search path entries:\n\
      {"\n".intercalate <| sp.map (·.toString)}"


def findOLeanParts (mod : Name) : ImportStateM (Array System.FilePath) := do
  let mFile ← findOLean' mod
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {mod} does not exist"
  let mut fnames := #[mFile]
  -- Opportunistically load all available parts.
  -- Necessary because the import level may be upgraded a later import.
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  return fnames


def readModuleData' (fname : System.FilePath) : ImportStateM (ModuleData × CompactedRegion) := do
  match (← moduleDataCache.get).get? fname with
  | some data => pure data
  | none =>
    let new := (← readModuleData fname)
    updateModuleDataCache fname new
    return new


def readModuleDataParts' (fnames : Array System.FilePath) : ImportStateM (Array (ModuleData × CompactedRegion)) := do
  let mut dataParts := #[]
  let mut reload := false
  for fname in fnames do
    match (← moduleDataCache.get).get? fname with
    | some data => dataParts := dataParts.push data
    | none =>
      reload := true
      dataParts ← readModuleDataParts fnames -- Have to load all parts together since otherwise Lean crashes (it's usually just the corresponding `.olean` and `.olean.private` files, so not too much overhead)
      break

  if reload then
    for (fname, data) in fnames.zip dataParts do
      updateModuleDataCache fname data

  return dataParts

partial def importModulesCore'
    (imports : Array Import) (globalLevel : OLeanLevel := .private)
    (arts : NameMap ImportArtifacts := {}) (isExported : Bool := globalLevel < .private)  :
    ImportStateM Unit := do
  go imports (importAll := true) (isExported := isExported) (needsData := true) (needsIRTrans := false)
  if globalLevel < .private then
    for i in imports do
      if let some (mod : ModuleData) := (ImportState.moduleNameMap (← get))[i.module]?.bind (·.mainModule?) then
        if !mod.isModule then
          throw <| IO.userError s!"cannot import non-`module` {i.module} from `module`"


/-
When the module system is disabled for the root, we import all transitively referenced modules and
ignore any module system annotations on the way.

When the module system is enabled for the root, each module may need to be imported at one of the
following levels:

* all: import public information into public scope and private information into private scope
* public: import public information into public scope
* privateAll: import public and private information into private scope
* private: import public information into private scope
* none: do not import any `.olean*`

These levels form a lattice in the following way:

* all > public > private > none
* all > privateAll > private > none

The level at which a module then is to be imported based on the given `import` relations is
determined by the least fixed point of the following rules:

* Root ≥ all
* A ≥ privateAll ∧ A `import all` B → B ≥ privateAll
* A ≥ private ∧ A `public (meta)? import` B → B ≥ private
* A ≥ public ∧ A `public (meta)? import` B → B ≥ public
* A ≥ privateAll ∧ A `(meta)? import` B → B ≥ private

As imports are a DAG, we may need to visit the same module multiple times until its minimum
necessary level is established.

The `meta` flag is special in that it only affects whether IR is needed. The rules for determining
this are as follows:

* A ≥ privateAll ∧ `meta import` B → needsIRTrans(B)
* A ≥ private ∧ A `public meta import` B → needsIRTrans(B)
* needsIRTrans(A) ∧ A `(public)? (meta)? import (all)?` B → needsIRTrans(B)

Note that in particular, A `meta import` B `import` C implies A `meta import` C, but
A `import` B `meta import` C does not.

As a final special case, we also load IR for `import all`, but non-transitively, to provide the same
information as for the current module.

* A ≥ privateAll → needsIR(A)
* needsIRTrans(A) → needsIR(A)

For implementation purposes, we represent elements in the lattice using two flags as follows:

* all = isExported && importAll
* privateAll = !isExported && importAll
* private = !isExported && !importAll
* public = isExported && !importAll

When neither `needsIR(A)` nor `A != none` is true, the module is not visited at all and missing from
the module map.
-/
where
  go (imports : Array Import) (importAll isExported needsData needsIRTrans : Bool) : ImportStateM PUnit := do
    for i in imports do
      -- `B > none`?
      let needsData := needsData && (i.isExported || importAll)
      -- `B ≥ privateAll`?
      let importAll := globalLevel == .private || importAll && i.importAll
      -- `B ≥ public`?
      let isExported := isExported && i.isExported
      let needsIRTrans := needsIRTrans || needsData && i.isMeta
      let needsIR := needsIRTrans || importAll || globalLevel > .exported
      if !needsData && !needsIR then
        continue

      let irPhases : IRPhases :=
        if importAll then .all
        else if needsIRTrans then .comptime  -- `globalLevel` should *not* be considered here
        else .runtime

      let goRec (mod : ImportedModule) : ImportStateM PUnit := do
        if let some mod := mod.mainModule? then
          go (importAll := importAll) (isExported := isExported) (needsData := needsData) (needsIRTrans := needsIRTrans) mod.imports

      if let some mod := (ImportState.moduleNameMap (← get))[i.module]? then
        -- when module is already imported, bump flags
        let importAll := importAll || mod.importAll
        let isExported := isExported || mod.isExported
        let needsData := needsData || ImportedModule.needsData mod
        let needsIRTrans := needsIRTrans || ImportedModule.needsIRTrans mod
        let needsIR := needsIRTrans || importAll
        let irPhases := if irPhases == mod.irPhases then irPhases else .all
        let parts ← if needsData && (ImportedModule.parts mod).isEmpty then loadData i else pure (ImportedModule.parts mod)
        let irData? ← if needsIR && (ImportedModule.irData? mod).isNone then loadIR? i else pure (ImportedModule.irData? mod)
        if importAll != mod.importAll || isExported != mod.isExported ||
            needsIRTrans != ImportedModule.needsIRTrans mod || needsData != ImportedModule.needsData mod || irPhases != mod.irPhases then
          modify fun (s : ImportState) =>
            let impmod := ImportedModule.mk {(ImportedModule.toEffectiveImport mod) with importAll, isExported, irPhases} parts irData? needsData needsIRTrans
            let s' := ImportState.moduleNameMap s |>.insert i.module impmod
            let state := ImportState.mk s' <| ImportState.moduleNames s
            state

          -- bump entire closure
          goRec mod
        continue

      -- newly discovered module
      let parts ← if needsData then loadData i else pure #[]
      let irData? ← if needsIR then loadIR? i else pure none
      let mod := ImportedModule.mk {i with importAll, isExported, irPhases} parts irData? needsData needsIRTrans
      goRec mod
      modify fun (s : ImportState) =>
        ImportState.mk (ImportState.moduleNameMap s |>.insert i.module mod) ((ImportState.moduleNames s).push i.module)
  loadData i := do
    let fnames ← if let some arts := arts.find? i.module then
      -- Opportunistically load all available parts.
      -- Producer (e.g., Lake) should limit parts to the proper import level.
      pure (arts.oleanParts (inServer := globalLevel ≥ .server))
    else
      findOLeanParts i.module
    readModuleDataParts' fnames
  loadIR? i := do
    let irFile? ← if let some arts := arts.find? i.module then
      pure arts.ir?
    else
      let irFile := (← findOLean' i.module).withExtension "ir"
      pure (guard (← irFile.pathExists) *> irFile)
    irFile?.mapM (readModuleData' ·)



/--
Creates environment object from given imports.

If `leakEnv` is true, we mark the environment as persistent, which means it will not be freed. We
set this when the object would survive until the end of the process anyway. In exchange, RC updates
are avoided, which is especially important when they would be atomic because the environment is
shared across threads (potentially, storing it in an `IO.Ref` is sufficient for marking it as such).

If `loadExts` is true, we initialize the environment extensions using the imported data. Doing so
may use the interpreter and thus is only safe to do after calling `enableInitializersExecution`; see
also caveats there. If not set, every extension will have its initial value as its state. While the
environment's constant map can be accessed without `loadExts`, many functions that take
`Environment` or are in a monad carrying it such as `CoreM` may not function properly without it.

If `level` is `exported`, the module to be elaborated is assumed to be participating in the module
system and imports will be restricted accordingly. If it is `server`, the data for
`getModuleEntries (includeServer := true)` is loaded as well. If it is `private`, all data is loaded
as if no `module` annotations were present in the imports.
-/
def importModules' (imports : Array Import) (opts : Options) (trustLevel : UInt32 := 0)
    (plugins : Array System.FilePath := #[]) (leakEnv := false) (loadExts := false)
    (level := OLeanLevel.private) (arts : NameMap ImportArtifacts := {})
    : IO Environment := do
  for imp in imports do
    if imp.module matches .anonymous then
      throw $ IO.userError "import failed, trying to import module with anonymous name"

  withImporting do
    plugins.forM Lean.loadPlugin
    -- let (_, s, env) ← timeit "importCore" <| ImportStateM'.run (importModulesCore' (globalLevel := level) imports arts) env
    let (_, s) ← ImportStateM.run (importModulesCore' (globalLevel := level) imports arts)
    finalizeImport (leakEnv := leakEnv) (loadExts := loadExts) (level := level) s imports opts trustLevel




/-
Mathlib.LinearAlgebra.RootSystem.Basic:250:38: error: Application type mismatch: The argument
  root
has type
  ι ↪ M
of sort `Type (max u_1 u_3)` but is expected to have type
  M
of sort `Type u_3` in the application
  (RootPairing.equiv_of_mapsTo p) root
, Mathlib.LinearAlgebra.RootSystem.Basic:246:4: error: (kernel) declaration has metavariables 'RootPairing.mk'''
])
[RootSystem.mk'] (#[])
[] (#[Mathlib.LinearAlgebra.RootSystem.Basic:258:5: error: Function expected at
  mk'' p root coroot hp hs
but this term has type
  RootPairing ι k M N

Note: Expected a function because this term is being applied to the argument
  hsp
-/
