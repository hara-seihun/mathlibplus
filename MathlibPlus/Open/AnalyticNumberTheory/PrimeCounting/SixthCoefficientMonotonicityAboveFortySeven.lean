import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 729: the displayed derivative of `Q` is positive above `log 47`,
its endpoint value has the stated strict margin, and the resulting sixth-
coefficient majorant is strictly increasing from `47` onward. -/
def sixthCoefficientMonotonicityAboveFortySeven : Prop :=
  let η : ℝ := 0.024334
  let F₆ : ℝ → ℝ := fun x =>
    let L := Real.log x
    x / L + x / L ^ 2 + 2 * x / L ^ 3 +
      6.024334 * x / L ^ 4 +
      24.024334 * x / L ^ 5 +
      120 * x / L ^ 6 +
      720 * x / L ^ 7 +
      6097.2 * x / L ^ 8
  let Q : ℝ → ℝ := fun L =>
    L ^ 8 + η * L ^ 3 * (L ^ 2 - 3 * L - 5) +
      1057.2 * L - 48777.6
  (∀ L : ℝ, Real.log 47 ≤ L →
      HasDerivAt Q
        (8 * L ^ 7 + η * L ^ 2 * (5 * L ^ 2 - 12 * L - 15) +
          1057.2) L ∧
      0 < 8 * L ^ 7 + η * L ^ 2 * (5 * L ^ 2 - 12 * L - 15) +
        1057.2) ∧
    Q (Real.log 47) > 3576.13 ∧
    StrictMonoOn F₆ (Set.Ici 47)

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
