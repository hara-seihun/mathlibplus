import Mathlib

open scoped BigOperators ENNReal Topology
open MeasureTheory
open Filter

noncomputable section

namespace MathlibPlus.Open.Formalization.K0127

/-- The Gaussian-node polynomial associated with the positive, strictly ordered nodes. -/
def gaussianZeroPolynomial (y : ℕ → ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.Icc 1 n).prod (fun j => x - (y n j) ^ 2)

/-- The normalized empirical measure of the Gaussian nodes. -/
def gaussianNodeMeasure (y : ℕ → ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  ((n : ℝ≥0∞)⁻¹) • (Finset.Icc 1 n).sum (fun j => Measure.dirac (y n j))

/--
The negative-axis ratio asymptotic is equivalent to convergence of the
Gaussian-node log potentials.
-/
def logPotentialConvergenceGaussianZeros
    (y : ℕ → ℕ → ℝ) (ρ : ℝ → ℝ)
    (_h_nodes : ∀ n : ℕ,
      (∀ j ∈ Finset.Icc 1 n, 0 < y n j) ∧
      (∀ j ∈ Finset.Icc 1 n, ∀ k ∈ Finset.Icc 1 n, j < k → y n k < y n j)) : Prop :=
  (∀ s s₀ : ℝ, 0 < s → 0 < s₀ →
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log
            (gaussianZeroPolynomial y n (-s) /
              gaussianZeroPolynomial y n (-s₀)))
        atTop
        (𝓝 (∫ z, Real.log ((s + z ^ 2) / (s₀ + z ^ 2)) * ρ z))) ↔
    (∀ s s₀ : ℝ, 0 < s → 0 < s₀ →
      Tendsto
        (fun n : ℕ =>
          ∫ y', Real.log ((s + y' ^ 2) / (s₀ + y' ^ 2)) ∂(gaussianNodeMeasure y n))
        atTop
        (𝓝 (∫ z, Real.log ((s + z ^ 2) / (s₀ + z ^ 2)) * ρ z)))

end MathlibPlus.Open.Formalization.K0127
