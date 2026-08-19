import MathlibPlus.Open.ResearchFormalizationBatch_01a0014a312d7fbea2e4a2da353f9ad6
import MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers

namespace MathlibPlus.Analysis.Claim10000

noncomputable section

/-- Claim 10000: the completed multiplier of an exact annular source is
invariant under the completed-source reflection `s ↦ 1 - s`. -/
def claim10000_completedSourceMultiplierReflection : Prop :=
  ∀ (a R : ℝ), 0 < a → a < R →
    ∀ f : ℝ → ℝ,
      f ∈
          MathlibPlus.Open.ResearchFormalizationBatch_01a0014a312d7fbea2e4a2da353f9ad6.annularZeroMeanSourceClass
            a R →
        ∀ s : ℂ,
          let E_f : ℂ → ℂ := fun z =>
            (1 / 2 : ℂ) *
              (MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.sourceMellin f z /
                  MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor z +
                MathlibPlus.Open.ResearchFormalization.O0328LogDerivativeAndFibers.sourceMellin
                    f (1 - z) /
                  MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor (1 - z))
          E_f (1 - s) = E_f s

end

end MathlibPlus.Analysis.Claim10000
