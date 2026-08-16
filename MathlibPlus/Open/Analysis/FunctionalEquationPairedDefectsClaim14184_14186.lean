import Mathlib

open MeasureTheory
open scoped ENNReal

namespace MathlibPlus.Open.Analysis

/-- The paired translation and reciprocal diagonal block on the positive Hilbert sum `H ⊕ H`. -/
def functionalEquationPairedBlock_claim14184 : Prop :=
  ∀ (a : ℝ) (lam : ℂ),
    a ≠ 0 →
    let H : Type := Lp ℂ 2 (volume : Measure ℝ)
    let H₂ : Type := WithLp (2 : ℝ≥0∞) (H × H)
    ∀ (τ : H ≃ₗᵢ[ℂ] H),
      (∀ f : H,
        (τ f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + a)) →
      ∃ (T : H₂ ≃ₗᵢ[ℂ] H₂) (D : H₂ →L[ℂ] H₂),
        (∀ u : H₂,
          T u =
            WithLp.toLp (2 : ℝ≥0∞)
              (τ (WithLp.ofLp u).1, τ (WithLp.ofLp u).2)) ∧
          (∀ u : H₂,
            D u =
              WithLp.toLp (2 : ℝ≥0∞)
                (Complex.exp ((a : ℂ) * lam) • (WithLp.ofLp u).1,
                  Complex.exp (-((a : ℂ) * star lam)) • (WithLp.ofLp u).2))

/-- Positive Hilbert energy adds the reciprocal-channel boundary defects without cancellation. -/
def positiveNormPairedDefect_claim14186 : Prop :=
  ∀ (lam : ℂ) (p : ℕ),
    Nat.Prime p →
    let beta : ℝ := lam.re
    let a : ℝ := Real.log (p : ℝ)
    let r : ℝ := Real.exp (a * beta)
    let H : Type := Lp ℂ 2 (volume : Measure ℝ)
    let H₂ : Type := WithLp (2 : ℝ≥0∞) (H × H)
    ∀ (τ : H ≃ₗᵢ[ℂ] H),
      (∀ h : H,
        (τ h : ℝ → ℂ) =ᵐ[volume] fun x => h (x + a)) →
      ∀ (f g : H),
        let u : H₂ := WithLp.toLp (2 : ℝ≥0∞) (f, g)
        let T : H₂ → H₂ := fun v =>
          WithLp.toLp (2 : ℝ≥0∞)
            (τ (WithLp.ofLp v).1, τ (WithLp.ofLp v).2)
        let D : H₂ → H₂ := fun v =>
          WithLp.toLp (2 : ℝ≥0∞)
            (Complex.exp ((a : ℂ) * lam) • (WithLp.ofLp v).1,
              Complex.exp (-((a : ℂ) * star lam)) • (WithLp.ofLp v).2)
        ‖T u - D u‖ ^ 2 =
            ‖τ f - Complex.exp ((a : ℂ) * lam) • f‖ ^ 2 +
              ‖τ g - Complex.exp (-((a : ℂ) * star lam)) • g‖ ^ 2 ∧
          (r - 1) ^ 2 * ‖f‖ ^ 2 + (r⁻¹ - 1) ^ 2 * ‖g‖ ^ 2 ≤
            ‖T u - D u‖ ^ 2

end MathlibPlus.Open.Analysis
