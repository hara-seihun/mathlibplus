import MathlibPlus.Open.NewResearch2.O0328

open Set

namespace MathlibPlus.Open.ResearchFormalization.O0328FullCarrier

noncomputable section

/-- A carrier is globally hyperbolic in the centered variable when all of its
zeros lie on the real `z`-axis. -/
def globallyHyperbolic (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F z = 0 → z.im = 0

/-- Claim 15479: the exact full carrier `Xi · E_q` has infinitely many
off-real zeros for every nonzero source in the admitted center-flat class, so
no such carrier is globally hyperbolic. -/
def claim15479_noGloballyHyperbolicFullCarrier : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈ MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass a R →
            q ≠ 0 →
              Set.Infinite
                  {z : ℂ |
                    MathlibPlus.Open.NewResearch2.O0328.fullMellinCarrier q z = 0 ∧
                      z.im ≠ 0} ∧
                ¬ globallyHyperbolic
                  (MathlibPlus.Open.NewResearch2.O0328.fullMellinCarrier q)

end

end MathlibPlus.Open.ResearchFormalization.O0328FullCarrier
