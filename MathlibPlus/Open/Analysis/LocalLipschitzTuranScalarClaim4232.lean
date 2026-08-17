import MathlibPlus.Open.Analysis.PolarizedTuranClaim4225
import MathlibPlus.Open.Analysis.ResearchFormalizationBatch_01a001aa

namespace MathlibPlus.Open.Analysis.LocalLipschitzTuranScalarClaim4232

/-- Claim 4232: local Lipschitz continuity of the complete Poisson Turan
scalar, together with the resulting first-shift graph-norm convergence. -/
def localLipschitzTuranScalar : Prop :=
  ∀ (x : ℝ),
    0 < x →
    (∀ (u v : ℕ → ℂ),
      poissonGraphFinite_claim4227 x u →
      poissonGraphFinite_claim4227 x v →
        ‖MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
              x u -
            MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
              x v‖ ≤
          (1 + Real.sqrt 2 + x ^ (-(1 / 2 : ℝ))) *
            poissonGraphNorm_claim4227 x (u - v) *
              (poissonGraphNorm_claim4227 x u +
                poissonGraphNorm_claim4227 x v)) ∧
    (∀ (u : ℕ → ℂ) (s : ℕ → ℕ → ℂ),
      poissonGraphFinite_claim4227 x u →
      (∀ k : ℕ, poissonGraphFinite_claim4227 x (s k)) →
      Filter.Tendsto
          (fun k : ℕ => poissonGraphNorm_claim4227 x (s k - u))
          Filter.atTop (nhds 0) →
      Filter.Tendsto
        (fun k : ℕ =>
          MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
            x (s k))
        Filter.atTop
        (nhds
          (MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.turanScalar
            x u)))

end MathlibPlus.Open.Analysis.LocalLipschitzTuranScalarClaim4232
