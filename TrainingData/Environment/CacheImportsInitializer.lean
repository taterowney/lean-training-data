module
import all Lean.Environment
public import Lean.Attributes
import Lean

public section

open Lean System


initialize oleanPathCache : IO.Ref (Std.HashMap Name FilePath) ← IO.mkRef {}
initialize moduleDataCache : IO.Ref (Std.HashMap System.FilePath (ModuleData × CompactedRegion)) ← IO.mkRef {}

def updateOleanPathCache (mod : Name) (path : FilePath) : IO Unit := do
  oleanPathCache.modify (·.insert mod path)

def updateModuleDataCache (path : System.FilePath) (data : ModuleData × CompactedRegion) : IO Unit := do
  moduleDataCache.modify (·.insert path data)

end
