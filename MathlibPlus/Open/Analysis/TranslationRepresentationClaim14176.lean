import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Claim 14176: a nonzero real shift on complex `L²(ℝ, dx)` has a unitary
translation whose almost-everywhere representative is `f (x + a)`. -/
def translationRepresentation_claim14176 : Prop :=
  ∀ {a : ℝ}, a ≠ 0 →
    ∃ τ :
        Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
          Lp ℂ 2 (volume : Measure ℝ),
      ∀ f : Lp ℂ 2 (volume : Measure ℝ),
        (τ f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + a)

end MathlibPlus.Open.Analysis
