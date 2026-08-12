import Mathlib

namespace MathlibPlus.GraphTheory.Claim37821

/-- Three disjoint finite pieces with the displayed cardinalities have the
claimed exact total valency. -/
theorem exact_valency_claim37821
    {α : Type*} [DecidableEq α]
    (r : ℕ) (A B C : Finset α)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hA : A.card = 8)
    (hB : B.card = 2 * (2 ^ (r - 1) - 1))
    (hC : C.card = 2 ^ (r - 1)) :
    (A ∪ B ∪ C).card = 6 + 3 * 2 ^ (r - 1) := by
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.2 ⟨hAC, hBC⟩
  rw [Finset.card_union_of_disjoint hABC,
    Finset.card_union_of_disjoint hAB, hA, hB, hC]
  have ht : 1 ≤ 2 ^ (r - 1) := Nat.one_le_pow (r - 1) 2 (by norm_num)
  omega

end MathlibPlus.GraphTheory.Claim37821
