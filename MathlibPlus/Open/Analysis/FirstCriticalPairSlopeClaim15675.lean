import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- Claim 15675: under RH, a certified simple lowest positive critical-line
zero has the unique largest slope, with the conjugate zero as the only other
zero attaining that slope.  The source carrier is kept inline rather than
introduced as a separate public definition. -/
def firstCriticalPairUniqueLargestRHSlope_claim15675 : Prop :=
  let nontrivialZero : ℂ → Prop := fun ρ =>
    riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
  let positiveZero : ℂ → Prop := fun ρ =>
    nontrivialZero ρ ∧ 0 < ρ.im
  let slope : ℂ → ℝ := fun ρ => ‖1 / (ρ - 1)‖ ^ 2
  RiemannHypothesis →
    ∀ (ρ₁ : ℂ) (γ₁ : ℝ),
      positiveZero ρ₁ →
      0 < γ₁ →
      ρ₁ = (1 / 2 : ℂ) + (γ₁ : ℂ) * Complex.I →
      deriv riemannZeta ρ₁ ≠ 0 →
      (∀ ρ : ℂ, positiveZero ρ → γ₁ ≤ ρ.im) →
        let d₁ : ℝ := slope ρ₁
        d₁ = 1 / (γ₁ ^ 2 + (1 / 4 : ℝ)) ∧
          (∀ ρ : ℂ, nontrivialZero ρ → slope ρ ≤ d₁) ∧
          (∀ ρ : ℂ, nontrivialZero ρ →
            slope ρ = d₁ → ρ = ρ₁ ∨ ρ = star ρ₁)

end MathlibPlus.Open.Analysis
