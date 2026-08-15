import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch019ffedb

/-- Claim 3500: multiplicative perturbations have stable projective logarithmic derivative. -/
def multiplicativePerturbationStability : Prop :=
  ∀ (S S₀ B B₀ eS eB : ℂ → ℂ) (z : ℂ),
    (DifferentiableAt ℂ S z ∧
      DifferentiableAt ℂ S₀ z ∧
      DifferentiableAt ℂ B z ∧
      DifferentiableAt ℂ B₀ z ∧
      DifferentiableAt ℂ eS z ∧
      DifferentiableAt ℂ eB z) →
    S = (fun w => S₀ w * (1 + eS w)) →
    B = (fun w => B₀ w * (1 + eB w)) →
    S z ≠ 0 ∧ S₀ z ≠ 0 ∧ B z ≠ 0 ∧ B₀ z ≠ 0 →
    ‖eS z‖ < (1 / 2 : ℝ) ∧ ‖eB z‖ < (1 / 2 : ℝ) →
    let logDerivative : (ℂ → ℂ) → ℂ → ℂ :=
      fun f w => deriv f w / f w
    let η : ℂ → ℂ := fun w => logDerivative (fun u => -B u / S u) w
    let η₀ : ℂ → ℂ := fun w => logDerivative (fun u => -B₀ u / S₀ u) w
    (η z - η₀ z =
        logDerivative (fun u => 1 + eB u) z -
          logDerivative (fun u => 1 + eS u) z) ∧
      ‖η z - η₀ z‖ ≤ 2 * ‖deriv eB z‖ + 2 * ‖deriv eS z‖

/-- Claim 3506: a positive vertical charge gives a unique regular equator graph. -/
def uniqueEquatorGraphFromVerticalCharge : Prop :=
  ∀ (I : Set ℝ) (y₀ y₁ τ₀ L : ℝ) (S B : ℂ → ℂ) (U : Set ℂ),
    Set.OrdConnected I →
    0 < L →
    y₀ < y₁ →
    0 < τ₀ →
    IsOpen U →
    {z : ℂ | z.re ∈ I ∧ z.im ∈ Set.Icc y₀ y₁} ⊆ U →
    DifferentiableOn ℂ S U →
    DifferentiableOn ℂ B U →
    (∀ z : ℂ, z ∈ U → S z ≠ 0 ∧ B z ≠ 0) →
    let σ : ℂ → ℂ := fun z => -B z / S z
    let a : ℝ → ℝ → ℝ := fun x y =>
      L⁻¹ * Real.log ‖σ ((x : ℂ) + (y : ℂ) * Complex.I)‖
    (∀ x : ℝ, x ∈ I → a x y₀ < 0 ∧ 0 < a x y₁) →
    (∀ x : ℝ, x ∈ I → ∀ y : ℝ, y ∈ Set.Icc y₀ y₁ →
      τ₀ ≤ deriv (fun t : ℝ => a x t) y) →
    ∃ g : ℝ → ℝ,
      (∀ x : ℝ, x ∈ I →
        y₀ < g x ∧ g x < y₁ ∧
        a x (g x) = 0 ∧
        DifferentiableAt ℝ g x ∧
        deriv g x =
          -deriv (fun t : ℝ => a t (g x)) x /
            deriv (fun t : ℝ => a x t) (g x)) ∧
      (∀ h : ℝ → ℝ,
        (∀ x : ℝ, x ∈ I →
          y₀ < h x ∧ h x < y₁ ∧
          a x (h x) = 0 ∧
          DifferentiableAt ℝ h x ∧
          deriv h x =
            -deriv (fun t : ℝ => a t (h x)) x /
              deriv (fun t : ℝ => a x t) (h x)) →
        ∀ x : ℝ, x ∈ I → h x = g x)

end MathlibPlus.Open.ResearchFormalizationBatch019ffedb
