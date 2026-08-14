import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.CertificateArithmetic

/-- Retained normalization and exact additive coefficient from Claim 1589. -/
def retainedNormalizationExactAdditiveCoefficient_1589 : Prop :=
  let c : ℝ := (22077 : ℝ) / 125000
  let C₂ : ℝ := (3161 : ℝ) / 200
  let D : ℝ := C₂ - c * Real.log (2 * Real.pi)
  C₂ = (15.805 : ℝ) ∧
    (∀ T : ℝ, 1 ≤ T →
      c * Real.log (T / (2 * Real.pi)) + C₂ = c * Real.log T + D) ∧
    (15.4804 : ℝ) < D ∧ D < (15.4805 : ℝ)

end MathlibPlus.Open.AnalyticNumberTheory.CertificateArithmetic
