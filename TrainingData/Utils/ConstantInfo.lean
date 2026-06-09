module

public import Lean.Environment

public section

namespace Lean.ConstantInfo

/-- Get the name of the module that a `ConstantInfo` lives in. -/
def getModule' (ci : ConstantInfo) (env : Environment) : Name := Id.run do
  let some idx := env.getModuleIdxFor? ci.name | return .anonymous
  env.allImportedModuleNames[idx]!

/-- Get the name of the module that a `ConstantInfo` lives in. -/
def getModule [Monad m] [MonadEnv m] (ci : ConstantInfo) : m Name := do
  let env ← getEnv
  pure $ getModule' ci env

/-- Heuristic to determine if a `ConstantInfo` represents an internal declaration (auxiliary constant, etc.)

TODO: isRec, isMatcher, etc. -/
def isInternal (ci : ConstantInfo) : Bool :=
  (ci.name.isInternalOrNum) ||
  (ci.name.isInaccessibleUserName) ||
  (ci.name.isAnonymous)


end Lean.ConstantInfo
end
