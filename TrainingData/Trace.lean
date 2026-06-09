module

public import TrainingData.Utils.Frontend
public import TrainingData.Environment.CacheImports
public import TrainingData.InfoTree.Basic
public import TrainingData.Normalize
public import Cli
public import TrainingData.Utils.MLList


public section

open Lean IO System Lean.Elab.IO


/--
Simpler and faster version of `parseImports`. From `Lean.Elab.ParseImportsFast`
-/
def Lean.parseImports'' (input : String) (fileName : String) : IO ParseImports.State := do
  let s := ParseImports.main input (ParseImports.whitespace input {})
  let some err := s.error?
    | return s
  let fileMap := input.toFileMap
  let pos := fileMap.toPosition s.pos
  throw <| .userError s!"{fileName}:{pos.line}:{pos.column}: {err}"

/-- Remove the header (`import` statements and module stuff) from Lean source code. -/
def Lean.removeHeader (input : String) : String :=
  let s := ParseImports.main input (ParseImports.whitespace input {})
  if s.error? == none then
    input.drop (s.pos.byteIdx - 2) |>.toString -- Idk why we need the `2` here, but it seems to work
  else
    input




/-- From a root module, recursively finds all imported modules, reads their source files, and returns an array of triples of the form (module name, list of imports, source file contents). The `predicate` argument can be used to filter which modules are included.
TODO: way to make this lazy so that we don't have to open and close everything twice? -/
partial def collectDependenciesParsed (root : Name) (predicate : Name → Bool := root.getRoot.isPrefixOf) : IO $ Array $ Name × Array Import × IO String := do
  let (out, _) ← go root predicate #[] {}
  return out
where
  go root predicate acc (seen : Std.HashSet Name) : IO (Array (Name × Array Import × IO String) × Std.HashSet Name) := do
    if seen.contains root || !predicate root then
      return (acc, seen)
    else
      let filePath ← findLean' root
      let src ← IO.FS.readFile filePath
      let header ← Lean.parseImports'' src root.toString
      let mut acc := acc.push (root, header.imports, IO.FS.readFile filePath)
      let mut seen := seen.insert root
      for imp in header.imports do
        (acc, seen) ← go imp.module predicate acc seen
      return (acc, seen)

/-- Recursively traces the modules starting from a root module, optionally skipping meta modules. -/
unsafe def traceModules (root : Name) (skipMeta := true)
  (predicate : Name → Bool := fun n => root.getRoot.isPrefixOf n && (!skipMeta || (!n.components.contains `Tactic && !n.components.contains `Lean && !n.components.contains `Std && !n.components.contains `Util))) :
  IO $ MLList IO (Name × MLList IO CompilationStep) := do
  enableInitializersExecution
  initMetaSearchPath

  let out := MLList.ofArray (m := IO) (← collectDependenciesParsed root predicate) |>.mapM
    fun (root, imports, src) => do
      let env ← importModules' imports {} (loadExts := true) (level := OLeanLevel.exported)
      let src := removeHeader (← src)
      return (root, processInput' src env (fileName := root.toString))
  pure out
