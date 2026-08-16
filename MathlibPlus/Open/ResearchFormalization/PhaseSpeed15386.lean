import Mathlib

open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.PhaseSpeed15386

noncomputable section

/-- Claim 15386: the real and phase gradients on a holomorphic logarithm
chart agree with the projective logarithmic-derivative speed, including the
oriented arclength identity on regular zero components. -/
def phaseSpeedOnRegularStokesArc_claim15386 : Prop :=
  ∀ (U : Set ℂ) (Pi : ℂ → ℂ) (u θ : ℂ → ℝ) (ω : ℂ → ℂ),
    IsOpen U →
    IsSimplyConnected U →
    DifferentiableOn ℂ Pi U →
    DifferentiableOn ℝ u U →
    DifferentiableOn ℝ θ U →
    (∀ z : ℂ, z ∈ U →
      Pi z ≠ 0 ∧
        Complex.exp ((u z : ℂ) + Complex.I * (θ z : ℂ)) = Pi z) →
    (∀ z : ℂ, z ∈ U → ω z = deriv Pi z / Pi z) →
    (∀ z : ℂ, z ∈ U →
      u z = Real.log ‖Pi z‖ ∧
        (fderiv ℝ u z ≠ 0 ↔ ω z ≠ 0) ∧
        ‖fderiv ℝ u z‖ = ‖ω z‖) ∧
    (∀ (γ : ℝ → ℂ) (a b : ℝ), a < b →
      Set.InjOn γ (Set.Icc a b) →
      (∀ s : ℝ, s ∈ Set.Icc a b → γ s ∈ U) →
      (∀ s : ℝ, s ∈ Set.Ioo a b → u (γ s) = 0) →
      (∀ s : ℝ, s ∈ Set.Ioo a b → ‖deriv γ s‖ = 1) →
      (∀ s : ℝ, s ∈ Set.Ioo a b →
        0 ≤ deriv (fun r : ℝ => θ (γ r)) s) →
      (∀ s : ℝ, s ∈ Set.Ioo a b →
        fderiv ℝ u (γ s) ≠ 0) →
      (∀ s : ℝ, s ∈ Set.Ioo a b →
        deriv (fun r : ℝ => θ (γ r)) s = ‖ω (γ s)‖))

end

end MathlibPlus.Open.ResearchFormalization.PhaseSpeed15386
