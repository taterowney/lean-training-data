module

public import Batteries.Data.MLList.Basic

public section

namespace MLList

/-- Run a lazy list in a `ReaderT` monad on some fixed state. -/
partial def runReaderT [Monad m] (L : MLList (ReaderT.{u, u} ρ m) α) (r : ρ) : MLList m α :=
  squash fun _ =>
    return match ← (uncons L).run r with
    | none => nil
    | some (a, L') => cons a (L'.runReaderT r)

/-- Run a lazy list in a `StateRefT'` monad on some initial state. -/
partial def runStateRefT [Monad m] [MonadLiftT (ST ω) m] (L : MLList (StateRefT' ω σ m) α) (s : σ) :
    MLList m α :=
  squash fun _ =>
    return match ← (uncons L).run s with
    | (none, _) => nil
    | (some (a, L'), s') => cons a (L'.runStateRefT s')


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

end
