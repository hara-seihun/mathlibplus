import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 6029: retain the interval, nonvanishing carrier, and the displayed
first two logarithmic derivatives before asserting unit modulus of the carrier
phase. -/
def claim6029_carrierPhaseUnitModulus : Prop :=
  ∀ (I : Set ℝ), Set.OrdConnected I →
    ∀ (A : ℝ → ℂ),
      (∀ t : ℝ, t ∈ I → A t ≠ 0) →
      (∀ t : ℝ, t ∈ I → DifferentiableAt ℝ A t) →
      (∀ t : ℝ, t ∈ I →
        DifferentiableAt ℝ (fun u : ℝ => deriv A u / A u) t) →
      let a : ℝ → ℂ := fun t => deriv A t / A t
      let b : ℝ → ℂ := fun t => deriv a t
      let ω : ℝ → ℂ := fun t => A t / (‖A t‖ : ℂ)
      let p : ℝ → ℝ := fun t => (a t).im
      let c : ℝ → ℝ := fun t => 2 * (p t) ^ 2 - (b t).re
      ∀ t : ℝ, t ∈ I → ‖ω t‖ = 1

end

end MathlibPlus.Analysis
