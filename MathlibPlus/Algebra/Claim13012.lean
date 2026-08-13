import Mathlib

namespace MathlibPlus.Algebra.Claim13012

/-- The cubic equation in the corrected inversion has the real solution obtained by
multiplying `A` by `2^(-1/3)`.  The source's definitions of `V` and `A` are not
needed for this exact algebraic consequence. -/
theorem corrected_cubic_scaling (A V : ℝ)
    (hV : V ^ 3 = A ^ 3 / 2) :
    V = (2 : ℝ) ^ (-1 / 3 : ℝ) * A := by
  have hc : ((2 : ℝ) ^ (-1 / 3 : ℝ)) ^ 3 = (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hscaled : ((2 : ℝ) ^ (-1 / 3 : ℝ) * A) ^ 3 = A ^ 3 / 2 := by
    rw [mul_pow, hc]
    ring
  apply (Odd.pow_injective (by norm_num : Odd 3))
  exact hV.trans hscaled.symm

end MathlibPlus.Algebra.Claim13012
