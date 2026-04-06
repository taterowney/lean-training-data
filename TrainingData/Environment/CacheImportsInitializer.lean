import Lean
import Batteries.Tactic.OpenPrivate

open Lean System


open private ImportState.mk from Lean.Environment


initialize oleanPathCache : IO.Ref (Std.HashMap Name FilePath) ← IO.mkRef {}
initialize moduleDataCache : IO.Ref (Std.HashMap System.FilePath (ModuleData × CompactedRegion)) ← IO.mkRef {}

def updateOleanPathCache (mod : Name) (path : FilePath) : IO Unit := do
  oleanPathCache.modify (·.insert mod path)

def updateModuleDataCache (path : System.FilePath) (data : ModuleData × CompactedRegion) : IO Unit := do
  moduleDataCache.modify (·.insert path data)
