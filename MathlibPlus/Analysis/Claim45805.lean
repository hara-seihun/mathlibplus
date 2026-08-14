import Mathlib

namespace MathlibPlus.Analysis.Claim45805

/-- The uniform variance of the exact three-bit witness from claim 45805. -/
theorem variance_threeBitWitness_claim45805 :
    let g : Fin 8 → ℚ := ![(-1 : ℚ), -1, -1, 2 / 3, 1, -2 / 3, 1, 1]
    let mean : ℚ := (∑ i, g i) / 8
    let variance : ℚ := (∑ i, (g i - mean) ^ 2) / 8
    variance = 31 / 36 := by
  dsimp
  norm_num [Fin.sum_univ_succ]

end MathlibPlus.Analysis.Claim45805
