import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Open.ResearchFormalization.O0328InfiniteNonrealZeros15478

noncomputable section

/-- Claim 15478: every nonzero source in the admitted center-flat class has
infinitely many off-axis zeros of its centered multiplier. -/
def claim15478 : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈
              MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
                a R →
            q ≠ (0 : ℝ → ℝ) →
              Set.Infinite
                {z : ℂ |
                  MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.centeredMultiplier
                      q z = 0 ∧
                    z.im ≠ 0}

end

end MathlibPlus.Open.ResearchFormalization.O0328InfiniteNonrealZeros15478
