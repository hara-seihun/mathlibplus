import Mathlib

namespace MathlibPlus.Analysis.Claim51211

/-- The exact scaled-literal inequalities in the interior and at both endpoints.
The source's policy quantities `Psi` and `R` are not defined in the admitted
claim, so this arithmetic core does not invent their latency/reserve interface. -/
theorem scaledLiteralBounds_claim51211
    {alpha Q : ℝ} (hα0 : 0 ≤ alpha) (hα1 : alpha ≤ 1)
    (hQ : alpha ≤ Q) :
    alpha ^ 2 * (Q + 1) ≤ alpha * (1 + alpha) * Q ∧
      alpha * (1 + alpha) * Q ≤ (1 + alpha) * Q := by
  have hQ0 : 0 ≤ Q := le_trans hα0 hQ
  have hleft : 0 ≤ alpha * (Q - alpha) :=
    mul_nonneg hα0 (sub_nonneg.mpr hQ)
  have hright : 0 ≤ (1 + alpha) * (1 - alpha) * Q := by
    exact mul_nonneg
      (mul_nonneg (by linarith) (sub_nonneg.mpr hα1)) hQ0
  constructor <;> nlinarith

end MathlibPlus.Analysis.Claim51211
