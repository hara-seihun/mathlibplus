import Mathlib

/-!
# Compact prime-counting denominator algebra

An exact polynomial residual certificate extracted from source record `C-0055`.
The imported analytic and finite-computation inputs used elsewhere in that packet
are deliberately not encoded as hypotheses here.
-/

namespace MathlibPlus.CompactPrimeCounting

/-- The normalized polynomial associated with the packet's compact denominator. -/
def compactPolynomial (A t : ℝ) : ℝ :=
  1 - t - t ^ 2 - 3 * t ^ 3 - A * t ^ 4

/-- Exact residual factorization for `A = 44.053`, together with strict positivity
for every positive `t`. -/
theorem compactResidual_44053 (t : ℝ) :
    1 - compactPolynomial ((44053 : ℝ) / 1000) t *
        (1 + t + 2 * t ^ 2 + 6 * t ^ 3 + 55 * t ^ 4) =
      t ^ 4 / 1000 *
        (53 + 111053 * t + 161106 * t ^ 2 +
          429318 * t ^ 3 + 2422915 * t ^ 4) ∧
    (0 < t → 0 <
      1 - compactPolynomial ((44053 : ℝ) / 1000) t *
        (1 + t + 2 * t ^ 2 + 6 * t ^ 3 + 55 * t ^ 4)) := by
  constructor
  · simp only [compactPolynomial]
    ring
  · intro ht
    rw [show
      1 - compactPolynomial ((44053 : ℝ) / 1000) t *
          (1 + t + 2 * t ^ 2 + 6 * t ^ 3 + 55 * t ^ 4) =
        t ^ 4 / 1000 *
          (53 + 111053 * t + 161106 * t ^ 2 +
            429318 * t ^ 3 + 2422915 * t ^ 4) by
      simp only [compactPolynomial]
      ring]
    positivity

end MathlibPlus.CompactPrimeCounting
