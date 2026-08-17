import MathlibPlus.Open.Analysis.DyadicMobiusEnergy

namespace MathlibPlus.Open.ResearchFormalization.R2616.Claim42824

open MathlibPlus.Open.Analysis

/-- Claim 42824: in the exact critical coordinates, the full field is the
pointwise `(I - q τ)` image of the odd field. -/
def claim42824 : Prop :=
  ∀ y : ℝ,
    criticalFullField y =
      criticalOddField y -
        criticalDyadicQ * criticalOddField (y - Real.log 2)

end MathlibPlus.Open.ResearchFormalization.R2616.Claim42824
