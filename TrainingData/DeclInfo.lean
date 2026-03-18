import Lean
import Cli
import Mathlib.Data.Real.Basic


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
    !(excludedRoots.contains modRoot)

/-- Prints all nontrivial declarations in the project. -/
unsafe def getConstants
    (projectName : Name := `Mathlib)
    (excludedRoots : Std.HashSet String := defaultExcludedRootSet) : IO Unit := do
  let env ← loadProject projectName
  env.constants.map₁.foldM (init := ()) fun _ n ci => do
    if isNontrivialDecl excludedRoots env n ci then
      let obj := Json.mkObj [("declaration", toJson n)]
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
    p, project : String;        "Root module to inspect (for example: `Mathlib`, `AutoTactic`)."
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
    p, project : String;        "Root module to inspect (for example: `Mathlib`, `AutoTactic`)."
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
    p, project : String;        "Root module to inspect (for example: `Mathlib`, `AutoTactic`)."
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
    p, project : String;        "Root module to inspect (for example: `Mathlib`, `AutoTactic`)."
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
    p, project : String;        "Root module to inspect (for example: `Mathlib`, `AutoTactic`)."
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
    goalStatesCmd;
    relativeDirectoryCmd;
    relativeDependenciesCmd;
    declFrequenciesCmd
]

/-- `lake exe declinfo` -/
def main (args : List String) : IO UInt32 :=
  declInfoCmd.validate args
