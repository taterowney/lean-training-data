module
import all Lean.Environment
public import Lean.Attributes
import Lean

public section

open Lean System


initialize oleanPathCache : IO.Ref (Std.HashMap Name FilePath) ← IO.mkRef {}
initialize moduleDataCache : IO.Ref (Std.HashMap System.FilePath (ModuleData × CompactedRegion)) ← IO.mkRef {}
initialize loadedModules : IO.Ref (Std.HashMap Name (Array FilePath)) ← IO.mkRef {}

def updateOleanPathCache (mod : Name) (path : FilePath) : IO Unit := do
  oleanPathCache.modify (·.insert mod path)

def updateModuleDataCache (path : System.FilePath) (data : ModuleData × CompactedRegion) : IO Unit := do
  moduleDataCache.modify (·.insert path data)

def updateLoadedModulesCache (mod : Name) (paths : Array FilePath) : IO Unit := do
  loadedModules.modify fun map => map.insert mod (paths ++ (map.get? mod).getD #[])

end
