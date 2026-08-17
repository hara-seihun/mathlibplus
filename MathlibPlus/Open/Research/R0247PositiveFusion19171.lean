import MathlibPlus.Open.ResearchFormalization.R0247FiniteRapidityDefect19175

open MeasureTheory

namespace MathlibPlus.Open.Research.R0247PositiveFusion19171

noncomputable section

/-- Claim 19171: the positive common-amplitude fused representation uses the
finite-rapidity cosh/sinh coordinates, has strict Lorentz defect wherever the
amplitude is positive, and records both sector weights as the displayed
integrals. -/
def claim19171_positiveCommonAmplitudeFusedRepresentation : Prop :=
  ∀ (A ξ : ℝ → ℝ),
    MathlibPlus.Open.ResearchFormalization.R0247FiniteRapidityDefect19175.finiteRapidityRepresentation A ξ →
      ∃ (E O : ℝ → ℝ) (wE wO : ℝ),
        (∀ ω : ℝ,
          E ω = Real.cosh (ξ ω) ∧ O ω = Real.sinh (ξ ω)) ∧
          (∀ ω : ℝ, 0 < A ω → E ω > |O ω|) ∧
            wE = ∫ ω : ℝ, A ω * E ω ∧
              wO = ∫ ω : ℝ, A ω * O ω

end

end MathlibPlus.Open.Research.R0247PositiveFusion19171
