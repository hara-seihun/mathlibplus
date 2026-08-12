import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MathlibPlus.Algebra.Claim12505

/-! The source fixes an integer parameter `N ≥ 4` and writes down the
cyclic mixed-shell polynomial `E_N`; the analytic and Toeplitz consequences
are separate claims and are not added here. -/

/-- The cyclic mixed-shell polynomial family from claim 12505. -/
noncomputable def cyclicMixedShellPolynomial
    (N : ℤ) (hN : 4 ≤ N) : Polynomial ℝ :=
  ((1 : Polynomial ℝ) + Polynomial.X) *
    ((1 : Polynomial ℝ) +
      Polynomial.C (2 * Real.cos (2 * Real.pi / (N : ℝ))) * Polynomial.X +
        Polynomial.X ^ 2)

end MathlibPlus.Algebra.Claim12505
