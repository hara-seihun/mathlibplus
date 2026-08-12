import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12041

/-- The exact rank-two, shift-one block and its three maximal two-by-two cofactors.
The row deletion order is the natural order on `Fin 3`. -/
theorem exactMaximalCofactors :
    let dneg : ℚ := 1287 / 128
    let d0 : ℚ := 1159 / 32
    let d1 : ℚ := 2101 / 24
    let d2 : ℚ := 191 / 2
    let B : Matrix (Fin 3) (Fin 2) ℚ :=
      !![d1, d2; d0, d1; dneg, d0]
    let delta0 : ℚ := B 1 0 * B 2 1 - B 1 1 * B 2 0
    let delta1 : ℚ := B 0 0 * B 2 1 - B 0 1 * B 2 0
    let delta2 : ℚ := B 0 0 * B 1 1 - B 0 1 * B 1 0
    delta0 = 13811 / 32 ∧
      delta1 = 212201 / 96 ∧
      delta2 = 302735 / 72 := by
  change
    (1159 / 32 : ℚ) * (1159 / 32) - (2101 / 24) * (1287 / 128) = 13811 / 32 ∧
      (2101 / 24 : ℚ) * (1159 / 32) - (191 / 2) * (1287 / 128) = 212201 / 96 ∧
      (2101 / 24 : ℚ) * (2101 / 24) - (191 / 2) * (1159 / 32) = 302735 / 72
  norm_num

end MathlibPlus.LinearAlgebra.Claim12041
