module
public import Lean.DeclarationRange

public section

namespace Lean

def findDeclarationRangesCore?' (env : Environment) (declName : Name) : Option DeclarationRanges :=
  -- In the case of private definitions imported via `import all`, looking in `.olean.server` is not
  -- sufficient, so we look in the actual environment as well via `exported` (TODO: rethink
  -- parameter naming).
  declRangeExt.find? (level := .exported) env declName <|>
    declRangeExt.find? (level := .server) env declName

/-- Find the declaration ranges (locations of corresponding source code) of a constant in an environment. -/
def findDeclarationRanges?' [Monad m] [MonadLiftT BaseIO m] (env : Environment) (declName : Name) : m (Option DeclarationRanges) := do
  let ranges ← if isAuxRecursor env declName || isNoConfusion env declName || isRecCore env declName then
    pure <| findDeclarationRangesCore?' env declName.getPrefix
  else
    pure <| findDeclarationRangesCore?' env declName
  match ranges with
  | none => return (← builtinDeclRanges.get (m := BaseIO)).find? declName
  | some _ => return ranges

namespace ConstantInfo

/-- Find the declaration ranges (locations of corresponding source code) of a constant in an environment. -/
def declarationRanges' [Monad m] [MonadLiftT BaseIO m] (ci : ConstantInfo) (env : Environment) : m (Option DeclarationRanges) := do
  findDeclarationRanges?' env ci.name

/-- Find the declaration ranges (locations of corresponding source code) of a constant in an environment. -/
def declarationRanges [Monad m] [MonadLiftT BaseIO m] [MonadEnv m] (ci : ConstantInfo) : m (Option DeclarationRanges) := do
  findDeclarationRanges? ci.name

end ConstantInfo

end Lean
end
