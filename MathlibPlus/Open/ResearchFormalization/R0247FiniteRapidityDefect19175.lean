import MathlibPlus.Open.NewResearch2.R0247Repair

namespace MathlibPlus.Open.ResearchFormalization.R0247FiniteRapidityDefect19175

open MeasureTheory

noncomputable section

/-- The exact finite-rapidity carrier for a positive common-amplitude fusion. -/
def finiteRapidityRepresentation (A ξ : ℝ → ℝ) : Prop :=
  (∀ ω : ℝ, 0 ≤ A ω) ∧
    Integrable (fun ω : ℝ => A ω * Real.cosh (ξ ω)) ∧
    Integrable (fun ω : ℝ => A ω * Real.sinh (ξ ω)) ∧
    ∃ ω : ℝ, 0 < A ω

/-- Claim 19175: at every positive-amplitude point of a finite-rapidity
representation, the even and odd relative coordinates have strict Lorentz
defect. -/
def claim19175 : Prop :=
  ∀ (A ξ : ℝ → ℝ),
    finiteRapidityRepresentation A ξ →
      ∀ ω : ℝ,
        0 < A ω →
          Real.cosh (ξ ω) > |Real.sinh (ξ ω)| ∧
            0 < (Real.cosh (ξ ω)) ^ 2 - (Real.sinh (ξ ω)) ^ 2

end

end MathlibPlus.Open.ResearchFormalization.R0247FiniteRapidityDefect19175
