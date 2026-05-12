import Mathlib

/-!
# `set_auto` — an automation tactic for Set-theoretic identities

This file defines a small combinator tactic that tries a battery of common
closing strategies. It is intended to discharge the kind of goals that appear
in `TrainingData/RetrievedRepresentativeDeclarations.lean` — identities and
iffs about `Set.image`, `Set.preimage`, `Set.iUnion`, `Set.ncard`, `Set.encard`,
`Pairwise`, etc.

The strategy is:
  1. try `rfl` / `trivial`;
  2. try `simp`-only normalisation with a set-flavoured simp set;
  3. fall back to `grind` after extensionality;
  4. fall back to `aesop`.

None of the steps make progress unless they fully close the goal, so the tactic
is safe to drop into a proof attempt without leaving partial states behind.
-/

open Lean Elab Tactic

namespace TrainingData

/-- Try a list of tactics; succeed with the first one that closes the goal. -/
syntax (name := setAuto) "set_auto" : tactic

macro_rules
  | `(tactic| set_auto) => `(tactic|
      first
        | rfl
        | (simp; done)
        | (simp_all; done)
        | (ext; simp_all; done)
        | (ext; simp_all; grind)
        | grind
        | aesop)

end TrainingData

/-! ## Smoke tests

These mirror the theorems in `RetrieveRepresentativeDeclarations.lean`. They
should all close with `set_auto` alone (or after a small amount of manual
rewriting that introduces the right shape). -/

section Tests
open Set TrainingData

example {α : Type*} {ι : α → Type*} {f : ∀ a, ι a} {t : ∀ a, Set (ι a)} :
    f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by set_auto

example (α : Type*) : (∅ : Set α).ncard = 0 := by set_auto

example {α β : Type*} {f : α → β} {s : Set β} :
    f ⁻¹' (range f ∩ s) = f ⁻¹' s := by set_auto

example {α : Type*} {ι : Type*} (s : ι → Set α) {β : Type*} (t : α → Set β) :
    ⋃ x ∈ ⋃ i, s i, t x = ⋃ (i) (x ∈ s i), t x := by set_auto

example {α β : Type*} {f : α → β} {s : Set (Set α)} :
    (f '' ⋃₀ s) = ⋃₀ (image f '' s) := by set_auto

example {α : Type*} (s : Finset α) :
    Set.encard (s : Set α) = s.card := by set_auto

example {ι α : Type*} {f : ι → α} :
    Pairwise (fun i j ↦ f i ≠ f j) ↔ f.Injective := by set_auto




/- New (outside of distribution/examples) problems -/

example {f : α → β} {s : Set β} : f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s := by
  set_auto

example (s : ι → Set (Set α)) : ⋃₀ ⋃ i, s i = ⋃ i, ⋃₀ s i := by
  set_auto

example {a : α} (h : a ∈ s) : ncard (insert a s) = s.ncard := by
  set_auto


end Tests
