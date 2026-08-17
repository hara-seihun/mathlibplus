import MathlibPlus.Open.Analysis.ResearchFormalizationBatch_01a001aa

namespace MathlibPlus.Open.Analysis.NegativeProductEstimateClaim4228

/-- Claim 4228: the negative shifted product is bounded by the two first-shift
Poisson graph norms on the finite graph space. -/
def negativeProductEstimate : Prop :=
  ∀ (x : ℝ) (u v : ℕ → ℂ),
    0 < x →
    poissonGraphFinite_claim4227 x u →
    poissonGraphFinite_claim4227 x v →
      (∑' n : ℕ,
        poissonWeight_claim4227 x n * ‖u (n + 1) * v (n + 1)‖) ≤
        poissonM1_claim4227 x u * poissonM1_claim4227 x v

end MathlibPlus.Open.Analysis.NegativeProductEstimateClaim4228
