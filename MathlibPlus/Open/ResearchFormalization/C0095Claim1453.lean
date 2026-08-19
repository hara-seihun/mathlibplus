import MathlibPlus.Open.ResearchBatch.C0095

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.C0095

/-- Claim 1453: the exact full-domain Riemann-zeta growth bound. -/
def exactFullDomainRiemannZetaGrowthBound_claim1453 : Prop :=
  ∀ (t σ : ℝ),
    |t| ≥ 3 →
    (1 / 2 : ℝ) ≤ σ →
    σ ≤ 1 →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      MathlibPlus.Open.ResearchBatch.C0095.bellottiAStar *
          Real.rpow |t|
            (MathlibPlus.Open.ResearchBatch.C0095.bellottiBStar *
              Real.rpow (1 - σ) (3 / 2 : ℝ)) *
        Real.rpow (Real.log |t|) (2 / 3 : ℝ)

end MathlibPlus.Open.ResearchFormalization.C0095
