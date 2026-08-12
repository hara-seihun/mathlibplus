import Mathlib

namespace MathlibPlus.Combinatorics.Claim30024

/-- The source's `𝔽₃²` and `𝔽₃³` are represented by finite additive
`ZMod 3` coordinate products. -/
theorem coefficientTableCount :
    Fintype.card ((ZMod 3 × ZMod 3) → ((ZMod 3 × ZMod 3) × ZMod 3)) =
      7_625_597_484_987 ∧
      (27 : ℕ) ^ 9 = 3 ^ 27 ∧
      (3 : ℕ) ^ 27 = 7_625_597_484_987 := by
  norm_num [Fintype.card_fun, Fintype.card_prod, ZMod.card]

end MathlibPlus.Combinatorics.Claim30024
