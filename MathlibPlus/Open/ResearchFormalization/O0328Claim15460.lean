import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Open.ResearchFormalization.O0328Claim15460

noncomputable section

open MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
open MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

/-- Claim 15460: the centered spectral coordinate and the arithmetic quotient
coordinate are the exact two presentations of the completed source multiplier. -/
def claim15460 : Prop :=
  ∀ (a R : ℝ), 0 < a → a < R →
    ∀ q : ℝ → ℝ,
      q ∈ centerFlatSourceClass a R →
        (∀ z : ℂ,
          centeredMultiplier q z =
            (1 / 2 : ℂ) *
              (sourceMellin q (centeredCoordinate z) /
                  MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor
                    (centeredCoordinate z) +
                sourceMellin q (1 - centeredCoordinate z) /
                  MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor
                    (1 - centeredCoordinate z))) ∧
        (∀ s : ℂ,
          arithmeticMultiplier q s =
            centeredMultiplier q
              (-Complex.I * (s - (1 / 2 : ℂ))))

end

end MathlibPlus.Open.ResearchFormalization.O0328Claim15460
