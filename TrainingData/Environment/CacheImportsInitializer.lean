import Lean
import Batteries.Tactic.OpenPrivate

open Lean System


open private ImportState.mk from Lean.Environment

-- initialize importStateCache : SimplePersistentEnvExtension (ImportState) (ImportState) ←
--   registerSimplePersistentEnvExtension {
--     name := `importStateCache

--     /- When a new entry is added, insert it into the map. -/
--     addEntryFn := fun _ new => new

--     /- When importing from other modules, merge the maps. -/
--     addImportedFn := fun imports =>
--       imports.flatten[0]?.getD (ImportState.mk {} #[])
--   }

-- initialize importStateCache : IO.Ref ImportState ← IO.mkRef (ImportState.mk {} #[])


initialize oleanPathCache : IO.Ref (Std.HashMap Name FilePath) ← IO.mkRef {}
initialize moduleDataCache : IO.Ref (Std.HashMap System.FilePath (ModuleData × CompactedRegion)) ← IO.mkRef {}

def updateOleanPathCache (mod : Name) (path : FilePath) : IO Unit := do
  oleanPathCache.modify (·.insert mod path)

def updateModuleDataCache (path : System.FilePath) (data : ModuleData × CompactedRegion) : IO Unit := do
  moduleDataCache.modify (·.insert path data)
