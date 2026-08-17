import MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Open.ResearchFormalization.O0328OddIntegerSample15472

noncomputable section

/-- Claim 15472: the centered multiplier at the prescribed imaginary sample
is the Mellin sample divided by twice the same completed gamma factor. -/
def claim15472 : Prop :=
  ∀ (a R : ℝ),
    0 < a →
    a < R →
      ∀ q : ℝ → ℝ,
        q ∈
            MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
              a R →
          ∀ n : ℕ,
            MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.centeredMultiplier
                q (-Complex.I * (2 * (n : ℂ) + (1 / 2 : ℂ))) =
              MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.sourceMellin
                  q (2 * (n : ℂ) + 1) /
                (2 *
                  MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor
                    (2 * (n : ℂ) + 1))

end

end MathlibPlus.Open.ResearchFormalization.O0328OddIntegerSample15472
