import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis

def derivativeCoefficientIdentity : Prop :=
  ∀ (Q : ℝ → ℝ) (Z : ℝ) (μ : Measure ℝ)
    (p : ℕ → Polynomial ℝ) (b : ℕ → ℝ),
    0 < Z →
    μ = Measure.withDensity volume
      (fun x : ℝ => ENNReal.ofReal (Z⁻¹ * Real.exp (-Q x))) →
    IsProbabilityMeasure μ →
    Measure.map (fun x : ℝ => -x) μ = μ →
    (∀ r : Polynomial ℝ, Integrable (fun x : ℝ => r.eval x) μ) →
    (∀ r : Polynomial ℝ,
      Integrable (fun x : ℝ => deriv Q x * r.eval x) μ ∧
      Filter.Tendsto
          (fun x : ℝ => r.eval x * Real.exp (-Q x))
          Filter.atTop (nhds 0) ∧
      Filter.Tendsto
          (fun x : ℝ => r.eval x * Real.exp (-Q x))
          Filter.atBot (nhds 0)) →
    (∀ x : ℝ, HasDerivAt Q (deriv Q x) x) →
    (∀ n : ℕ, p n ≠ 0 ∧ (p n).natDegree = n) →
    (∀ i j : ℕ,
      ∫ x : ℝ, (p i).eval x * (p j).eval x ∂μ =
        if i = j then (1 : ℝ) else 0) →
    (∀ n : ℕ, 0 < n →
      ∀ x : ℝ,
        x * (p n).eval x =
          b (n + 1) * (p (n + 1)).eval x +
            b n * (p (n - 1)).eval x) →
    (∀ n : ℕ, 0 < n → 0 < b n) →
    ∀ n : ℕ, 0 < n →
      (n : ℝ) / b n =
        ∫ x : ℝ,
          deriv Q x * (p n).eval x * (p (n - 1)).eval x ∂μ

end MathlibPlus.Open.Analysis
