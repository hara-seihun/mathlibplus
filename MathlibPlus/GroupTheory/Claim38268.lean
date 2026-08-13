import Mathlib
import Mathlib.GroupTheory.Coset.Card

namespace MathlibPlus.GroupTheory.Claim38268

/-- The Lagrange-order core of the order-21 subgroup-lattice claim.  The exact
seven-complement count and uniqueness of the order-seven subgroup remain
source-specific fidelity boundaries. -/
theorem subgroupOrderDivisors_claim38268
    {G : Type*} [Group G] (hG : Nat.card G = 21) (H : Subgroup G) :
    Nat.card H = 1 ∨ Nat.card H = 3 ∨ Nat.card H = 7 ∨ Nat.card H = 21 := by
  have hdvd : Nat.card H ∣ 21 := by
    rw [← hG]
    exact H.card_subgroup_dvd_card
  have hle : Nat.card H ≤ 21 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card H <;> norm_num at hdvd <;> simp_all

end MathlibPlus.GroupTheory.Claim38268
