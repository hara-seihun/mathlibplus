import Mathlib

namespace MathlibPlus.Analysis.Claim22039

/-- The derivative-square block from claim 22039 is a square when the carrier
phase has unit modulus.  `normSq` is the squared complex modulus. -/
theorem derivativeSquareBlock_nonneg (ω z : ℂ)
    (hω : Complex.normSq ω = 1) :
    Complex.normSq z + (ω ^ 2 * z ^ 2).re =
        2 * (ω * z).re ^ 2 ∧
      0 ≤ Complex.normSq z + (ω ^ 2 * z ^ 2).re := by
  have hω' : ω.re ^ 2 + ω.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hω
  have hident : Complex.normSq z + (ω ^ 2 * z ^ 2).re =
      2 * (ω * z).re ^ 2 := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      pow_two]
    have hcoef : 1 - ω.re ^ 2 - ω.im ^ 2 = 0 := by linarith [hω']
    calc
      z.re * z.re + z.im * z.im +
          ((ω.re * ω.re - ω.im * ω.im) * (z.re * z.re - z.im * z.im) -
            (ω.re * ω.im + ω.im * ω.re) * (z.re * z.im + z.im * z.re)) =
          2 * ((ω.re * z.re - ω.im * z.im) *
            (ω.re * z.re - ω.im * z.im)) +
            (1 - ω.re ^ 2 - ω.im ^ 2) * (z.re ^ 2 + z.im ^ 2) := by ring
      _ = 2 * ((ω.re * z.re - ω.im * z.im) *
            (ω.re * z.re - ω.im * z.im)) := by rw [hcoef, zero_mul, add_zero]
  exact ⟨hident, by rw [hident]; positivity⟩

end MathlibPlus.Analysis.Claim22039
