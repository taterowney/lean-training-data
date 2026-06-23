module

import Lean
public import TrainingData.Utils.FindSource
public import Lean.Elab.ParseImportsFast
public import Lake
-- The umbrella `Lake` does not re-export the workspace loader publicly, so import it directly.
import Lake.Load.Workspace/-!test -/

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
    input.toRawSubstring.extract s.pos input.rawEndPos |>.toString
  else
    input

def collectModuleParsed (mod : Name) : IO (Name × Array Import × IO String) := do
  let filePath ← findLean' mod
  let src ← IO.FS.readFile filePath
  let header ← Lean.parseImports'' src mod.toString
  return (mod, header.imports, IO.FS.readFile filePath)

/-- From a root module, recursively finds all imported modules, reads their source files, and returns an array of triples of the form (module name, list of imports, source file contents). The `predicate` argument can be used to filter which modules are included.
TODO: way to make this lazy so that we don't have to open and close everything twice? -/
partial def collectDependencies (roots : Array Name) (predicate : Name → Bool := fun _ => true) : IO $ Array $ Name × Array Import × IO String := do
  let mut out := #[]
  let mut seen := {}
  for root in roots do
    (out, seen) ← go root predicate #[] seen
  return out
where
  go root predicate acc (seen : Std.HashSet Name) : IO (Array (Name × Array Import × IO String) × Std.HashSet Name) := do
    if seen.contains root || !predicate root then
      return (acc, seen)
    else
      let new ← collectModuleParsed root
      let mut acc := acc.push new
      let mut seen := seen.insert root

      let imports := new.2.1
      for imp in imports do
        (acc, seen) ← go imp.module predicate acc seen
      return (acc, seen)

def collectDependenciesInProject (root : Name) (predicate : Name → Bool := fun n => root.getRoot.isPrefixOf n) : IO $ Array $ Name × Array Import × IO String := do
  collectDependencies #[root] predicate


initialize collectDependenciesCache : IO.Ref (Std.HashMap Name (Array Import × IO String)) ← IO.mkRef {}

partial def collectDependenciesCached (roots : Array Name) (predicate : Name → Bool := fun _ => true) : IO $ Array $ Name × Array Import × IO String := do
  let mut out := {}
  for root in roots do
    out ← go root out
  return out.toArray.filter fun (name, _) => predicate name
where
  go root acc : IO (Std.HashMap Name (Array Import × IO String)) := do
    if acc.contains root then
      return acc

    else if let some cached := (← collectDependenciesCache.get).get? root then
      return acc.insert root cached

    else
      let new ← collectModuleParsed root

      collectDependenciesCache.modify fun m => m.insert root new.2
      let mut acc := acc.insert root new.2

      let imports := new.2.1
      for imp in imports do
        acc ← go imp.module acc
      return acc

end
