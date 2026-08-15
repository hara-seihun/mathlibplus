import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.GeometricPrimeTower

noncomputable section

def perturbationSeries (d : ℝ) (p : ℕ) : ℝ :=
  ∑' k : {k : ℕ // 1 ≤ k},
    |(1 + d) ^ (k : ℕ) - 1| / (p : ℝ) ^ (k : ℕ)

def explicitPerturbationEnvelope (d : ℝ) (p : ℕ) : ℝ :=
  (|d| / (p : ℝ)) /
    (1 - (1 + |d|) / (p : ℝ)) ^ 2

def geometricPrimeTowerPerturbationBound : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧
    ∀ (d : ℝ) (p : ℕ), |d| ≤ (1 / 2 : ℝ) → 3 ≤ p →
      perturbationSeries d p ≤ C * (|d| / (p : ℝ))) ∧
  (∀ (d : ℝ) (p : ℕ), |d| ≤ (1 / 2 : ℝ) → 3 ≤ p →
    perturbationSeries d p ≤ explicitPerturbationEnvelope d p)

end

end MathlibPlus.Open.Analysis.GeometricPrimeTower
