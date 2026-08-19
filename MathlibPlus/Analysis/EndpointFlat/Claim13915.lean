import Mathlib

open MeasureTheory

namespace MathlibPlus.Analysis.EndpointFlat.Claim13915

/-- Claim 13915: the exact real even endpoint-flat quartic source and all
listed endpoint, integral, and derivative data. -/
def endpointFlatPolynomialSource_claim13915 : Prop :=
  let p : ℝ → ℝ := fun v => (1 - v ^ 2) * (v ^ 2 - 1 / 5)
  Function.Even p ∧
    (∀ v : ℝ, p v = -v ^ 4 + (6 / 5) * v ^ 2 - 1 / 5) ∧
    p 1 = 0 ∧
    (∫ v in (-1 : ℝ)..1, p v) = 0 ∧
    HasDerivAt p (-8 / 5) 1

end MathlibPlus.Analysis.EndpointFlat.Claim13915
