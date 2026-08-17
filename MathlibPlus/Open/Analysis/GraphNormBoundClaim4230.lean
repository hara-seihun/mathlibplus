import MathlibPlus.Open.Analysis.PolarizedTuranClaim4225
import MathlibPlus.Open.Analysis.ResearchFormalizationBatch_01a001aa

namespace MathlibPlus.Open.Analysis.GraphNormBoundClaim4230

/-- Claim 4230: the polarized Poisson Turan form obeys the stated graph-norm
bound with C_x = 1 + sqrt 2 + x^(-1/2). -/
def graphNormBound : Prop :=
  ∀ (x : ℝ) (u v : ℕ → ℂ),
    0 < x →
    poissonGraphFinite_claim4227 x u →
    poissonGraphFinite_claim4227 x v →
      ‖MathlibPlus.Open.Analysis.PolarizedTuranClaim4225.polarizedTuranForm
          x u v‖ ≤
        (1 + Real.sqrt 2 + x ^ (-(1 / 2 : ℝ))) *
          poissonGraphNorm_claim4227 x u * poissonGraphNorm_claim4227 x v

end MathlibPlus.Open.Analysis.GraphNormBoundClaim4230
