import Mathlib

namespace MathlibPlus.Combinatorics.Claim38093

/-- The numerical pullback receipt in the rank-four census. -/
theorem rank_four_pullback_arithmetic_claim38093 :
    (3 : ℕ) ^ 4 = 81 ∧ 6561 * 81 = 531441 := by
  norm_num

/-- An abstract product of a 6,561-element reduced census with an 81-element
fiber has the claimed 531,441-element total.  The source-specific quotient
map and its lift bijection remain external carriers. -/
theorem rank_four_product_census_claim38093 :
    Fintype.card (Fin 6561 × Fin 81) = 531441 := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

end MathlibPlus.Combinatorics.Claim38093
