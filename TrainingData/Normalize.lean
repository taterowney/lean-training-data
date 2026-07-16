module

public import Lean

open Lean Meta Elab

public section

namespace Lean.Expr

/-- Apply `f` to each subexpression, carrying a state `α` along the way. Proceeds depth-first, prioritizing deepest nodes.  -/
partial def traverseDFS_bottom_up {α : Type} [Monad m] (f : α → Expr → m (α × Expr)) (init : α) (e : Expr) : m Expr := do
  let (_, e) ← go init e
  return e
  where
  go (state : α) (e : Expr) : m (α × Expr) := do
    match e with
    | .lam n ty body bi    => do
      let (state, ty) ← go state ty
      let (state, body) ← go state body
      f state (.lam n ty body bi)
    | .forallE n ty body bi => do
      let (state, ty) ← go state ty
      let (state, body) ← go state body
      f state (.forallE n ty body bi)
    | .letE n ty val body nd => do
      let (state, ty) ← go state ty
      let (state, val) ← go state val
      let (state, body) ← go state body
      f state (.letE n ty val body nd)
    | .app fn arg           => do
      let (state, fn) ← go state fn
      let (state, arg) ← go state arg
      f state (.app fn arg)
    | .mdata d e'           => do
      let (state, e') ← go state e'
      f state (.mdata d e')
    | .proj s i e'          => do
      let (state, e') ← go state e'
      f state (.proj s i e')
    | e => f state e


/-- Apply `f` to each subexpression, carrying a state `α` along the way. Proceeds depth-first, but prioritizes the current node before its children. -/
partial def traverseDFS {α : Type} [Monad m] (f : α → Expr → m (α × Expr)) (init : α) (e : Expr) : m Expr := do
  let (_, e) ← go init e
  return e
  where
  go (state : α) (e : Expr) : m (α × Expr) := do
    let (state, e) ← f state e
    match e with
    | .lam n ty body bi    => do
      let (state, ty) ← go state ty
      let (state, body) ← go state body
      return (state, .lam n ty body bi)
    | .forallE n ty body bi => do
      let (state, ty) ← go state ty
      let (state, body) ← go state body
      return (state, .forallE n ty body bi)
    | .letE n ty val body nd => do
      let (state, ty) ← go state ty
      let (state, val) ← go state val
      let (state, body) ← go state body
      return (state, .letE n ty val body nd)
    | .app fn arg           => do
      let (state, fn) ← go state fn
      let (state, arg) ← go state arg
      return (state, .app fn arg)
    | .mdata d e'           => do
      let (state, e') ← go state e'
      return (state, .mdata d e')
    | .proj s i e'          => do
      let (state, e') ← go state e'
      return (state, .proj s i e')
    | e => return (state, e)



/-- α-rename bound variables to `x0`, `x1`, ... -/
partial def renameBinders (e : Expr) : MetaM Expr :=
  e.traverseDFS (fun n e => do
    let name := ("x" ++ toString n).toName
    match e with
    | .lam _ ty body bi    => return (n+1, .lam name ty body bi)
    | .forallE _ ty body bi => return (n+1, .forallE name ty body bi)
    | .letE _ ty val body nd => return (n+1, .letE name ty val body nd)
    | e => return (n, e)
  ) 0


def withPPOptions {m α} [Monad m] [MonadEnv m] [MonadWithOptions m] (x : m α) : m α := do
  withOptions (fun o => o
    |>.set `pp.notation false
    |>.set `pp.unicode false
    |>.set `pp.fullNames true
    |>.set `pp.funBinderTypes true
    |>.set `pp.numericTypes true
    |>.set `pp.coercions.types true
    |>.set `pp.letVarTypes true
    |>.set `pp.mvars false
    |>.set `pp.explicit false
    |>.set `pp.proofs false
    -- |>.set `pp.deepTerms true
    -- |>.set `pp.structureInstanceTypes true
  ) x

/- Reduce an Expr to as normal of a form as possible. Two defeq expressions should ideally be the same after this (modulo definitions and such) -/
def normalize (e : Expr) : MetaM Expr := do
  let e ← whnf e
  let e ← renameBinders e
  let e ← zetaReduce e
  let e ← Core.betaReduce e
  return e

/- Render an Expr to a string, normalizing it first. -/
def render (e : Expr) : MetaM String := do
  let e ← normalize e
  let out ← withPPOptions (PrettyPrinter.ppExpr e)
  let out := out.pretty (width := 100000000)
  return out

end Lean.Expr

namespace Lean.Elab.TacticInfo


/- From a TacticInfo, normalize and serialize the information about a tactic application, giving a list of premises, the current goal before applying the tactic, the goal after, and the source code with the current tactic replaced with a "sorry". -/
def pretty (info : TacticInfo) (declStx : Syntax) : MetaM (Array String × String × String × String) := do
  let goal_before_mvar ← info.goalsBefore.head?.getDM (throwError "Assertion failed: no goals")
  let goal_after_mvar := info.goalsAfter.head?

  let srcWithSorry ← declStx.replaceM (fun s => do
    if s.eqWithInfo info.stx then
      let out ← `(tactic| sorry)
      pure (some out)
    else
      pure none)
  let renderedSrc := srcWithSorry.prettyPrint.pretty'


  goal_before_mvar.withContext do
    let mut n := 0
    for premise? in (← getLCtx).decls do
      match premise? with
      | some premise => do
        goal_before_mvar.modifyLCtx fun ctx => ctx.setUserName premise.fvarId s!"h{n}".toName
        n := n + 1
      | none => continue

  goal_before_mvar.withContext do
    withExposedNames do
      let mut premises := #[]

      for premise? in (← getLCtx).decls do
        match premise? with
        | some premise => do
          let pp ← Expr.render (← instantiateMVars premise.type)
          if premise.hasValue then
            premises := premises.push s!"{premise.userName}: {pp} := {← Expr.render (← instantiateMVars premise.value)}\n"
          else
            premises := premises.push s!"{premise.userName}: {pp}\n"
        | none => continue

      let goal_before ← Expr.render (← instantiateMVars (← goal_before_mvar.getType))
      let goal_after ← match goal_after_mvar with
      | some g => Expr.render (← instantiateMVars (← g.getType))
      | none => pure "Goals accomplished!"
      return (premises, goal_before, goal_after, renderedSrc)


/- From a TacticInfo, normalize and serialize the information about a tactic application, giving a list of premises, the goal before applying the tactic, and the goal after. Runs from IO, but requires a ContextInfo to set up the MetaM environment -/
def pretty' (info : TacticInfo) (stepStx : Syntax) (ctx : ContextInfo) : IO (Array String × String × String × String) := do
  ctx.runMetaM {} <| Meta.withMCtx info.mctxBefore <| info.pretty stepStx

end Lean.Elab.TacticInfo

/-
- Keep ascii but get rid of unicode
- Skolemize
- Can eliminate unnecessary premises?
- Do we embed goals and hypotheses separately?
-/
