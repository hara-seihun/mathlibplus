import Mathlib
import MathlibPlus.Open.Analysis.LambertWInversionOfV

namespace MathlibPlus.Open.ResearchFormalization.Claim2040Lambert

noncomputable section

/-- The reviewed `V` carrier used by the principal-real Lambert inversion. -/
private def lambertV2040 (x : ℝ) : ℝ :=
  (Real.log x) ^ (2 / 3 : ℝ) *
    (Real.log (Real.log x)) ^ (1 / 3 : ℝ)

/-- Claim 2040: the logarithmic/exponential identity and its positive-
argument principal-real Lambert-W inversion are retained together. -/
def claim2040_exactLambertInversion : Prop :=
  (∀ x : ℝ, Real.exp 1 < x →
    let y := Real.log x
    let z := 2 * Real.log y
    lambertV2040 x ^ 3 = y ^ 2 * Real.log y ∧
      y ^ 2 * Real.log y = (1 / 2 : ℝ) * z * Real.exp z) ∧
  (∀ A x : ℝ, 0 < A → Real.exp 1 < x →
    (lambertV2040 x = A ↔
      Real.log (Real.log x) =
        (1 / 2 : ℝ) * MathlibPlus.Open.Analysis.principalLambertW (2 * A ^ 3)))

end

end MathlibPlus.Open.ResearchFormalization.Claim2040Lambert
