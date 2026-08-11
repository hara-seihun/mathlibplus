import Mathlib

namespace MathlibPlus.Analysis

/-- Claim 17415, written with `Complex.normSq` for the squared modulus. -/
theorem poleTermDiagonalization_claim17415 (A B : ℂ) :
    2 * (A * (starRingEnd ℂ) B).re =
      (1 / 2 : ℝ) * Complex.normSq (A + B) -
        (1 / 2 : ℝ) * Complex.normSq (A - B) := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re]
  ring

end MathlibPlus.Analysis
