import Mathlib

namespace MathlibPlus.Open.Analysis.FairSign

noncomputable section

open scoped BigOperators
open MeasureTheory

/-- The explicit entire characteristic-function data in the fair-sign factorization. -/
def fairSignFactorizationData (φ : ℂ → ℂ) (μ : Measure ℝ) (σ : ℝ)
    (a : ℕ → ℝ) : Prop :=
  Function.Even φ ∧
    Differentiable ℂ φ ∧
    IsProbabilityMeasure μ ∧
    (∀ t : ℝ, φ (t : ℂ) = charFun μ t) ∧
    0 ≤ σ ∧
    (∀ j : ℕ, 0 ≤ a j) ∧
    Summable (fun j : ℕ => (a j) ^ 2) ∧
    (∀ t : ℝ,
      φ (t : ℂ) =
        Complex.exp (-((σ : ℂ) ^ 2) * (t : ℂ) ^ 2 / 2) *
          ∏' j : ℕ, Complex.cos ((a j * t : ℝ) : ℂ))

/-- An even entire characteristic function of independent fair-sign type. -/
def fairSignFactorization (φ : ℂ → ℂ) : Prop :=
  ∃ (μ : Measure ℝ) (σ : ℝ) (a : ℕ → ℝ),
    fairSignFactorizationData φ μ σ a

/-- Nonzero cosine factors and square-summable amplitudes give a nonzero product. -/
def fairSignCosineProductNonvanishing : Prop :=
  ∀ (a : ℕ → ℝ) (γ : ℝ),
    γ ≠ 0 →
    Summable (fun j : ℕ => (a j) ^ 2) →
    (∀ j : ℕ, Real.cos (a j * γ) ≠ 0) →
    ∏' j : ℕ, Real.cos (a j * γ) ≠ 0

/-- Every nonzero zero of the factorization is supplied by one cosine factor. -/
def fairSignZeroHasCosineFactor : Prop :=
  ∀ (φ : ℂ → ℂ) (μ : Measure ℝ) (σ : ℝ) (a : ℕ → ℝ),
    fairSignFactorizationData φ μ σ a →
    ∀ γ : ℝ, γ ≠ 0 → φ (γ : ℂ) = 0 →
      ∃ (j₀ : ℕ) (k : ℤ),
        a j₀ * γ = ((2 * k + 1 : ℤ) : ℝ) * Real.pi / 2

/-- The cosine factor at a nonzero zero supplies every nonnegative odd rung. -/
def fairSignOddMultipleZeros : Prop :=
  ∀ (φ : ℂ → ℂ) (μ : Measure ℝ) (σ : ℝ) (a : ℕ → ℝ),
    fairSignFactorizationData φ μ σ a →
    ∀ γ : ℝ, γ ≠ 0 → φ (γ : ℂ) = 0 →
      ∀ m : ℕ,
        φ (((((2 * m + 1 : ℕ) : ℝ) * γ) : ℝ) : ℂ) = 0

/-- The nonzero real zero set is the union of the complete odd cosine ladders. -/
def fairSignZeroSetOddLadders : Prop :=
  ∀ (φ : ℂ → ℂ) (μ : Measure ℝ) (σ : ℝ) (a : ℕ → ℝ),
    fairSignFactorizationData φ μ σ a →
    ∀ t : ℝ, t ≠ 0 →
      (φ (t : ℂ) = 0 ↔
        ∃ (j : ℕ) (k : ℤ),
          a j * t = ((2 * k + 1 : ℤ) : ℝ) * Real.pi / 2)

end

end MathlibPlus.Open.Analysis.FairSign
