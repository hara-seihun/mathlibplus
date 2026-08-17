import MathlibPlus.Open.Analysis.DepthNormIdentityK0125

namespace MathlibPlus.Open.Analysis.LambertAntiderivativeK0125

open scoped Interval
open MathlibPlus.Open.Analysis.DepthNormIdentityK0125

noncomputable section

/-- Claim 8889: the compact Lambert-W antiderivative identity. -/
def claim_8889 : Prop :=
  ∀ N : ℝ, 0 < N →
    (∫ x in (0 : ℝ)..N, compactLambertW x) =
        2 * Real.pi *
          (Real.exp (compactLambertW N) *
              ((compactLambertW N) ^ 2 - compactLambertW N + 1) - 1) ∧
      (∫ x in (0 : ℝ)..N, compactLambertW x) =
        N * (compactLambertW N - 1 + (compactLambertW N)⁻¹) -
          2 * Real.pi

end

end MathlibPlus.Open.Analysis.LambertAntiderivativeK0125
