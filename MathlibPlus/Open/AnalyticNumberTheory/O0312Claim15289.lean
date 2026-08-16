import MathlibPlus.Open.Analysis.ZetaHardyFormalization

namespace MathlibPlus.Open.AnalyticNumberTheory.O0312Claim15289

open MathlibPlus.Open.Analysis.ZetaHardy

/-- Claim 15289.  For the finitely supported pole-cancelling complex
Dirichlet multiplier from O-0312, the product `A_c ζ` has the exact divisor
convolution coefficients in the half-plane of absolute convergence. -/
def claim15289 : Prop :=
  ∀ c : ℕ → ℂ,
    finiteComplexCoefficients c →
    poleCancellationCondition c →
    ∀ s : ℂ,
      1 < s.re →
      finiteDirichletMultiplier c s * riemannZeta s =
        ∑' n : ℕ,
          if 0 < n then
            divisorConvolutionCoefficient c n * (n : ℂ) ^ (-s)
          else 0

end MathlibPlus.Open.AnalyticNumberTheory.O0312Claim15289
