import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.HallSubgroup

/-!
The group-order core of claim 41841.  The source-specific regular
`E(C₃₅, 8)` permutation presentation and its ambient block-kernel
interpretation are intentionally not invented here.
-/

/-- A finite group of order `280 = 8 * 35` has no subgroup whose order is
 divisible by three. -/
theorem no_three_dvd_subgroup_of_order_280
    {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 280) (H : Subgroup G) :
    ¬ 3 ∣ Nat.card H := by
  intro hthree
  have hdiv : Nat.card H ∣ Nat.card G := H.card_subgroup_dvd_card
  have : (3 : ℕ) ∣ 280 := dvd_trans hthree (hG ▸ hdiv)
  norm_num at this

end MathlibPlus.GroupTheory.HallSubgroup
