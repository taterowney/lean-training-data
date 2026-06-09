module


public import Lean
public import Lean.DeclarationRange
public import Cli
public import Mathlib.Data.Real.Basic
public import TrainingData.Frontend

public section
open Lean Json Cli

unsafe def loadProject (projectName : Name := `Mathlib) : IO Environment := do
  enableInitializersExecution
  initSearchPath (← findSysroot)
  importModules #[projectName] {} (loadExts := true)

def Lean.ConstantInfo.isTheorem (ci : ConstantInfo) : Bool :=
  match ci with
  | .thmInfo _ => true
  | _ => false

def Lean.ConstantInfo.getModule (ci : ConstantInfo) (env : Environment) : Name := Id.run do
  let some idx := env.getModuleIdxFor? ci.name | return .anonymous
  env.allImportedModuleNames[idx]!

def defaultExcludedRoots : Array String :=
  #["Lean", "Init", "Std", "Batteries", "Qq", "Aesop", "_private"]

def defaultExcludedRootSet : Std.HashSet String :=
  defaultExcludedRoots.foldl (init := ({} : Std.HashSet String)) fun acc r => acc.insert r

def parseModuleName (raw : String) : Name :=
  ((raw.replace "/" ".").splitOn ".")
    |>.foldl (init := .anonymous) fun acc part =>
      if part.isEmpty then acc else .str acc part

def excludedRootsFrom (p : Parsed) : Std.HashSet String := Id.run do
  let roots : Array String := p.flag! "exclude-roots" |>.as! (Array String)
  let roots :=
    if p.hasFlag "include-private" then
      roots.filter (· != "_private")
    else
      roots
  roots.foldl (init := ({} : Std.HashSet String)) fun acc root => acc.insert root


def isNontrivialDecl
    (excludedRoots : Std.HashSet String)
    (env : Environment)
    (name : Name)
    (ci : ConstantInfo) : Bool :=
  let declRoot := name.getRoot.toString
  let modRoot := (ci.getModule env).getRoot.toString
  !(excludedRoots.contains declRoot) &&
    (ConstantInfo.isDefinition ci || ConstantInfo.isTheorem ci) &&
    !(excludedRoots.contains modRoot) &&
    -- (ci.name.components.getLast?.bind (fun last => if last.isStr && last.getString!.startsWith "_" then some false else some true)).getD true && -- last component of name shouldn't start with underscore
    !(ci.name.isInternalOrNum) &&
    !(ci.name.isInaccessibleUserName) &&
    !(ci.name.isAnonymous)


def findDeclarationRangesCore?' [Monad m] (env : Environment) (declName : Name) : m (Option DeclarationRanges) :=
  -- In the case of private definitions imported via `import all`, looking in `.olean.server` is not
  -- sufficient, so we look in the actual environment as well via `exported` (TODO: rethink
  -- parameter naming).
  return declRangeExt.find? (level := .exported) env declName <|>
    declRangeExt.find? (level := .server) env declName

def findDeclarationRanges?' [Monad m] [MonadLiftT BaseIO m] (env : Environment) (declName : Name) : m (Option DeclarationRanges) := do
  let ranges ← if isAuxRecursor env declName || isNoConfusion env declName || isRecCore env declName then
    findDeclarationRangesCore?' env declName.getPrefix
  else
    findDeclarationRangesCore?' env declName
  match ranges with
  | none => return (← builtinDeclRanges.get (m := BaseIO)).find? declName
  | some _ => return ranges


def Array.dedup {α : Type} [BEq α]  (arr : Array α) : Array α := Id.run do
  let mut seen := #[]
  let mut out := #[]
  for x in arr do
    if !seen.contains x then
      seen := seen.push x
      out := out.push x
  out


/-- Simple heuristic to obtain the open namespaces from a source string. Overshoots since it doesn't account for `section`s, `end`s, etc. -/
def getOpenNamespaces (src : String) : Array Name :=
  src.splitOn "\n" |>.toArray
    |>.filterMap (fun line => Id.run do
      let trimmed := line.trimAscii.toString
      if trimmed.startsWith "open " || trimmed.startsWith "namespace " then
        let mut ns := trimmed.splitOn " " |>.drop 1
        if ns[0]? == "scoped" then ns := ns.drop 1

        let mut out := #[]
        for part in ns do
          if part.isEmpty || part == "in" then break
          out := out.push part.toName
        some out
      else
        none)
    |>.flatten.dedup



/-- Prints all nontrivial declarations in the project. -/
unsafe def getConstants
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
  let env ← loadProject projectName
  env.constants.map₁.foldM (init := ()) fun _ n ci => do
    if isNontrivialDecl excludedRoots env n ci then
      let obj := Json.mkObj [("declaration", toJson n)]
      IO.println obj.compress

unsafe def getConstantsWithSource
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do

  let env ← loadProject projectName

  env.constants.map₁.foldM (init := ()) fun _ n ci => do
    if isNontrivialDecl excludedRoots env n ci && ci.isTheorem then
      let modName := ci.getModule env
      let modSrc := FileMap.ofString (← Lean.Elab.IO.moduleSource' modName)

      let some src ← findDeclarationRanges?' env n | return ()

      let start_pos := modSrc.ofPosition src.range.pos
      let end_pos := modSrc.ofPosition src.range.endPos
      let declSrc := some <| (modSrc.source.toRawSubstring.extract start_pos end_pos).toString

      let aboveSrc := (modSrc.source.toRawSubstring.extract 0 start_pos).toString
      let openNamespaces := getOpenNamespaces aboveSrc

      let obj := Json.mkObj [("declaration", toJson n), ("source", toJson (declSrc.getD "")), ("openNamespaces", toJson openNamespaces)]
      IO.println obj.compress

/-- Prints the initial goal states of all nontrivial declarations in the project. -/
unsafe def getDeclsInitialGoalStates
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
  let env ← loadProject projectName
  env.constants.map₁.foldM (init := ()) fun _ n ci => do
    if isNontrivialDecl excludedRoots env n ci then
      let obj := Json.mkObj [("declaration", toJson n), ("type", toJson (toString ci.type))]
      IO.println obj.compress

unsafe def compareAllDecls
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet)
    (fn : Environment → Name → ConstantInfo → Name → ConstantInfo → IO Unit) : IO Unit := do
  let env ← loadProject projectName
  let decls ← env.constants.map₁.foldM (init := #[]) fun acc n ci => do
    if isNontrivialDecl excludedRoots env n ci then
      return acc.push (n, ci)
    return acc
  for (n1, ci1) in decls do
    for (n2, ci2) in decls do
      fn env n1 ci1 n2 ci2

def formatResult {α : Type} [ToJson α]
    (n1 : Name)
    (n2 : Name)
    (comparisonKey : String)
    (comparisonValue : α) : IO Unit :=
  let json := mkObj [
    ("declaration1", toJson n1),
    ("declaration2", toJson n2),
    (comparisonKey, toJson comparisonValue)
  ]
  IO.println json.compress

/-- Scores declarations for similarity based on directory layout overlap. -/
unsafe def getDeclsRelativeDirectory
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
  compareAllDecls projectName excludedRoots fun env n1 _ n2 _ => do
    let some idx1 := env.getModuleIdxFor? n1 | return ()
    let some idx2 := env.getModuleIdxFor? n2 | return ()
    let mod1 := env.allImportedModuleNames[idx1]!
    let mod2 := env.allImportedModuleNames[idx2]!

    let mut score := 0
    for (part1, part2) in mod1.components.zip mod2.components do
      if part1 == part2 then score := score + 1 else break

    formatResult n1 n2 "relativeDirectory" score

/-- Scores declarations by shared dependency ratio. -/
unsafe def getDeclsRelativeDependencies
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
  compareAllDecls projectName excludedRoots fun _ n1 decl1 n2 decl2 => do
    let deps1 := decl1.getUsedConstantsAsSet
    let deps2 := decl2.getUsedConstantsAsSet

    let sharedDeps := deps1.filter fun d => deps2.contains d
    let totalDeps := deps1.size + deps2.size - sharedDeps.size
    let similarity : Float :=
      if totalDeps == 0 then 0 else sharedDeps.size.toFloat / totalDeps.toFloat
    formatResult n1 n2 "relativeDependencies" similarity

unsafe def writeDeclFrequencies
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
  let env ← loadProject projectName
  for (n, ci) in env.constants.map₁ do
    if isNontrivialDecl excludedRoots env n ci then
      let mut deps := ci.getUsedConstantsAsSet.toArray
      let obj := Json.mkObj [("declaration", toJson n), ("dependencies", toJson deps)]
      IO.println obj.compress

-- unsafe def writeDeclFrequencies
--     (projectName : Name := `Mathlib)
--     (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
--   IO.println "Tabulating declaration frequencies..."
--   let env ← loadProject projectName
--   let mut freqMap : Std.HashMap Name Nat := {}
--   for (n, ci) in env.constants.map₁ do
--     if isNontrivialDecl excludedRoots env n ci then
--       for dep in ci.getUsedConstantsAsSet.toArray do
--         freqMap := freqMap.insert dep (freqMap.getD dep 0 + 1)
--   let asJson := Json.mkObj (freqMap.toList.map fun (k, v) => (toString k, toJson v))
--   IO.FS.withFile "decl_frequencies.json" IO.FS.Mode.write fun handle => do
--     handle.putStrLn (toString asJson)
--   IO.println "...done!"

-- def getDeclFrequencies
--     (projectName : Name := `Mathlib)
--     (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
--   unless ← IO.FS.pathExists "decl_frequencies.json" do
--     unsafe writeDeclFrequencies projectName excludedRoots




def loadCliConfig (p : Parsed) : Name × Std.HashSet String :=
  let projectName := parseModuleName <| p.flag! "project" |>.as! String
  let excludedRoots := excludedRootsFrom p
  (projectName, excludedRoots)

def runConstantsCmd (p : Parsed) : IO UInt32 := do
  let (projectName, excludedRoots) := loadCliConfig p
  unsafe getConstants projectName excludedRoots
  return 0

def runConstantsWithSrcCmd (p : Parsed) : IO UInt32 := do
  let (projectName, excludedRoots) := loadCliConfig p
  unsafe getConstantsWithSource projectName excludedRoots
  return 0

def runGoalStatesCmd (p : Parsed) : IO UInt32 := do
  let (projectName, excludedRoots) := loadCliConfig p
  unsafe getDeclsInitialGoalStates projectName excludedRoots
  return 0

def runRelativeDirectoryCmd (p : Parsed) : IO UInt32 := do
  let (projectName, excludedRoots) := loadCliConfig p
  unsafe getDeclsRelativeDirectory projectName excludedRoots
  return 0

def runRelativeDependenciesCmd (p : Parsed) : IO UInt32 := do
  let (projectName, excludedRoots) := loadCliConfig p
  unsafe getDeclsRelativeDependencies projectName excludedRoots
  return 0

def runDeclFrequenciesCmd (p : Parsed) : IO UInt32 := do
  let (projectName, excludedRoots) := loadCliConfig p
  unsafe writeDeclFrequencies projectName excludedRoots
  return 0

def constantsCmd : Cmd := `[Cli|
  constants VIA runConstantsCmd;
  "Print each nontrivial declaration as newline-delimited JSON. Output format: JSON objects with fields `declaration` and `type`."

  FLAGS:
    p, project : String;        "Root module to inspect (for example: `Mathlib`)."
    e, "exclude-roots" : Array String; "Root namespaces/modules to filter out (comma-separated list)."
    "include-private";         "Include declarations rooted at `_private` even if listed in `--exclude-roots`."

  EXTENSIONS:
    defaultValues! #[
      ("project", "Mathlib"),
      ("exclude-roots", "Lean,Init,Std,Batteries,Qq,Aesop,_private")
    ]
]

def constantsAndSrcCmd : Cmd := `[Cli|
  constants_with_src VIA runConstantsWithSrcCmd;
  "Print each nontrivial declaration together with its source code as newline-delimited JSON. Output format: JSON objects with fields `declaration` and `source`."

  FLAGS:
    p, project : String;        "Root module to inspect (for example: `Mathlib`)."
    e, "exclude-roots" : Array String; "Root namespaces/modules to filter out (comma-separated list)."
    "include-private";         "Include declarations rooted at `_private` even if listed in `--exclude-roots`."

  EXTENSIONS:
    defaultValues! #[
      ("project", "Mathlib"),
      ("exclude-roots", "Lean,Init,Std,Batteries,Qq,Aesop,_private")
    ]
]

def goalStatesCmd : Cmd := `[Cli|
  "goal-states" VIA runGoalStatesCmd;
  "Print each nontrivial declaration and its type as newline-delimited JSON. Output format: JSON objects with fields `declaration` and `type`."

  FLAGS:
    p, project : String;        "Root module to inspect (for example: `Mathlib`)."
    e, "exclude-roots" : Array String; "Root namespaces/modules to filter out (comma-separated list)."
    "include-private";         "Include declarations rooted at `_private` even if listed in `--exclude-roots`."

  EXTENSIONS:
    defaultValues! #[
      ("project", "Mathlib"),
      ("exclude-roots", "Lean,Init,Std,Batteries,Qq,Aesop,_private")
    ]
]

def relativeDirectoryCmd : Cmd := `[Cli|
  "relative-directory" VIA runRelativeDirectoryCmd;
  "Compare declaration pairs by shared directory-prefix depth in their defining modules. Output is newline-delimited JSON with fields `declaration1`, `declaration2`, and `relativeDirectory` (a nonnegative integer)."

  FLAGS:
    p, project : String;        "Root module to inspect (for example: `Mathlib`)."
    e, "exclude-roots" : Array String; "Root namespaces/modules to filter out (comma-separated list)."
    "include-private";         "Include declarations rooted at `_private` even if listed in `--exclude-roots`."

  EXTENSIONS:
    defaultValues! #[
      ("project", "Mathlib"),
      ("exclude-roots", "Lean,Init,Std,Batteries,Qq,Aesop,_private")
    ]
]

def relativeDependenciesCmd : Cmd := `[Cli|
  "relative-dependencies" VIA runRelativeDependenciesCmd;
  "Compare declaration pairs by shared dependency overlap (Jaccard-style ratio). Output format: newline-delimited JSON with fields `declaration1`, `declaration2`, and `relativeDependencies` (a float between 0 and 1)."

  FLAGS:
    p, project : String;        "Root module to inspect (for example: `Mathlib`)."
    e, "exclude-roots" : Array String; "Root namespaces/modules to filter out (comma-separated list)."
    "include-private";         "Include declarations rooted at `_private` even if listed in `--exclude-roots`."

  EXTENSIONS:
    defaultValues! #[
      ("project", "Mathlib"),
      ("exclude-roots", "Lean,Init,Std,Batteries,Qq,Aesop,_private")
    ]
]

def declFrequenciesCmd : Cmd := `[Cli|
  "decl-frequencies" VIA runDeclFrequenciesCmd;
  "Count how many times each declaration is used as a dependency across the project. Output format: a single JSON object mapping declaration names to usage counts."

  FLAGS:
    p, project : String;        "Root module to inspect (for example: `Mathlib`)."
    e, "exclude-roots" : Array String; "Root namespaces/modules to filter out (comma-separated list)."
    "include-private";         "Include declarations rooted at `_private` even if listed in `--exclude-roots`."

  EXTENSIONS:
    defaultValues! #[
      ("project", "Mathlib"),
      ("exclude-roots", "Lean,Init,Std,Batteries,Qq,Aesop,_private")
    ]
]

def declInfoCmd : Cmd := `[Cli|
  declinfo NOOP; ["0.1.0"]
  "Command-line utilities for declaration inventory and pairwise similarity metrics."

  SUBCOMMANDS:
    constantsCmd;
    constantsAndSrcCmd;
    goalStatesCmd;
    relativeDirectoryCmd;
    relativeDependenciesCmd;
    declFrequenciesCmd
]

/-- `lake exe declinfo` -/
def main (args : List String) : IO UInt32 :=
  declInfoCmd.validate args
