import Lean
import Mathlib

open Lean IO System Meta Elab Command



#check Set.mem_univ_pi
#check Set.image2_right_comm
#check Set.ncard_empty
#check Set.nonempty_of_ncard_ne_zero
#check Set.preimage_range_inter
#check Set.biUnion_iUnion
#check Set.encard_pair
#check Set.encard_coe_eq_coe_finsetCard
#check pairwise_ne_iff_injective
#check Set.image_sUnion








open Set
theorem mem_univ_pi : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp

theorem image2_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image2 f (image2 g s t) u = image2 g' (image2 f' s u) t := by
  rw [image2_swap g, image2_swap g']
  exact image2_assoc fun _ _ _ => h_right_comm _ _ _

theorem ncard_empty (α : Type*) : (∅ : Set α).ncard = 0 := by
  rw [ncard_eq_zero]

theorem nonempty_of_ncard_ne_zero (hs : ncard s ≠ 0) : s.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at hs

theorem preimage_range_inter {f : α → β} {s : Set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s := by
  rw [inter_comm, preimage_inter_range]

theorem biUnion_iUnion (s : ι → Set α) (t : α → Set β) :
    ⋃ x ∈ ⋃ i, s i, t x = ⋃ (i) (x ∈ s i), t x := by simp [@iUnion_comm _ ι]

theorem encard_pair {x y : α} (hne : x ≠ y) : ({x, y} : Set α).encard = 2 := by
  rw [encard_insert_of_notMem (by simpa), ← one_add_one_eq_two,
    WithTop.add_right_inj WithTop.one_ne_top, encard_singleton]

theorem encard_coe_eq_coe_finsetCard (s : Finset α) :
    encard (s : Set α) = s.card := by
  rw [Finite.encard_eq_coe_toFinset_card (Finset.finite_toSet s)]; simp

lemma pairwise_ne_iff_injective' {f : ι → α} : Pairwise (fun i j ↦ f i ≠ f j) ↔ f.Injective := by
  simp
  constructor
  · intro h a b hf
    by_cases hneq : a ≠ b
    · have := h hneq
      simp at this
      contradiction
    simp at hneq
    exact hneq
  intro h1 a b hneq
  by_contra
  have := h1 this
  contradiction

theorem image_sUnion {f : α → β} {s : Set (Set α)} : (f '' ⋃₀ s) = ⋃₀ (image f '' s) := by
  ext
  simp only [Set.mem_iUnion, Set.sUnion_image]
  grind
