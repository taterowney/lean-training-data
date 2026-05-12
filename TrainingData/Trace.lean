import TrainingData.Frontend
import TrainingData.Environment.CacheImports
import TrainingData.InfoTree.Basic
import TrainingData.Normalize
import Cli


open Lean IO System Lean.Elab.IO




def Array.deduplicate [BEq α] (arr : Array α) : Array α := Id.run do
  let mut res : Array α := #[]
  for elem in arr do
    unless res.contains elem do
      res := res.push elem
  res

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


namespace MLList

/-- Repeatedly apply a function `f : α → m (Option (α × List β))` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list, and stopping on `none`.

(This variant allows starting with a specified `List β` of elements, as well. )-/
partial def fixlWith? [Monad m] {α β : Type u} (f : α → m (Option $ α × List β))
    (s : α) (l : List β) : MLList m β :=
  thunk fun _ =>
    match l with
    | b :: rest => cons b (fixlWith? f s rest)
    | [] => squash fun _ => do
      match ← f s with
      | none => pure nil
      | some (s', l) =>
        match l with
        | b :: rest => pure <| cons b (fixlWith? f s' rest)
        | [] => pure <| fixlWith? f s' []

/-- Repeatedly apply a function `f : α → m (Option (α × List β))` to an initial `a : α`,
accumulating the elements of the resulting `List β` as a single monadic lazy list. -/
def fixl? [Monad m] {α β : Type u} (f : α → m (Option $ α × List β)) (s : α) : MLList m β :=
  fixlWith? f s []

end MLList


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
      let filePath ← Lean.Elab.IO.findLean root
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

  let out := MLList.ofArray (m := IO) (← collectDependenciesParsed root predicate) |>.mapM
    fun (root, imports, src) => do
      let env ← importModules' imports {} (loadExts := true) (level := OLeanLevel.exported)
      let src := removeHeader (← src)
      return (root, processInput' src env (fileName := root.toString))
  pure out
