import MathlibPlus.Support.LambertJacobiCounting

namespace MathlibPlus.Open.Analysis

open MathlibPlus.Support.LambertJacobiCounting

/-- For every positive `κ`, the Lambert Jacobi spectral count has the admitted two-term asymptotic law. -/
def twoTermLambertJacobiCountingLaw : Prop :=
  ∀ (κ : ℝ), ∀ hκ : 0 < κ,
    Asymptotics.IsLittleO (Filter.atTop : Filter ℝ)
      (fun T : ℝ =>
        (lambertJacobiCount κ hκ T : ℝ) -
          T / (2 * Real.pi) * (Real.log (T / κ) - 1))
      (fun T : ℝ => T)

end MathlibPlus.Open.Analysis
