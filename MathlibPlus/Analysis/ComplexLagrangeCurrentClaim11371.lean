import Mathlib.Data.Complex.Basic

namespace MathlibPlus.Analysis

/-- Claim 11371: the complex Lagrange-current identity. `Complex.normSq` is
`|z|²`, and `star` is complex conjugation. -/
theorem complexLagrangeCurrent_identity (F F' : ℂ) :
    Complex.normSq F * Complex.normSq F' =
      (Complex.re (F' * star F)) ^ 2 + (Complex.im (F' * star F)) ^ 2 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

end MathlibPlus.Analysis
