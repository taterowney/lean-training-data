import Mathlib


-- open Real

-- theorem irrational_sqrt_2 : ¬ ∃ q : ℚ, √2 = q := sorry

open Group

theorem Cauchy_abelian {G : Type*} [CommGroup G] [Finite G] (p : ℕ) (hprime : Prime p) (hdiv : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := sorry
