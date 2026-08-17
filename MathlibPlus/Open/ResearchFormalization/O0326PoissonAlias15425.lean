import MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15424

namespace MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15425

open MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias

noncomputable section

/-- The converse estimate uses the real, even, exact-S0 endpoint-flat source
and the canonical literal/full Poisson defect.  The constant has indices
only for the Sobolev order and strip height; the scale, source family,
point, and action exponent remain quantified in the estimate. -/
def claim15425_quantitativeSobolevNormExplosion : Prop :=
  ∀ (N : ℕ) (Y : ℝ),
    2 ≤ N → Y < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧
        (∀ (β : ℝ) (q : ℝ → ℝ → ℝ) (z : ℝ → ℂ),
          (∀ L : ℝ, 0 < L →
            exactS0EndpointFlatSource L (q L)) →
            ∀ L : ℝ, 0 < L →
              ‖(z L).im‖ ≤ Y →
              Real.exp (-β * L) ≤
                ‖poissonDefect (q L) L (z L)‖ →
              derivativeL1Norm N (q L) ≥
                C⁻¹ *
                  Real.exp (((N : ℝ) - 1 / 2 - Y - β) * L)) ∧
        (∀ β : ℝ,
          (N : ℝ) > β + Y + 1 / 2 →
            0 < (N : ℝ) - 1 / 2 - Y - β)

end

end MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15425
