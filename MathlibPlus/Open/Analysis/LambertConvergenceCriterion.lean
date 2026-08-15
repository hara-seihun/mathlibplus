import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The principal real Lambert value on the nonnegative half-line, defined by its
    nonnegative inverse equation. -/
noncomputable def principalLambertW0 (x : ℝ) : ℝ :=
  if 0 ≤ x then sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = x} else 0

/-- The additive Lambert convergence criterion, including its logarithmic gauge. -/
noncomputable def additiveLambertConvergenceCriterion : Prop :=
  let W : ℕ → ℝ := fun j => principalLambertW0 ((j : ℝ) / (2 * Real.pi))
  let R : (ℕ → ℝ) → ℕ → ℝ :=
    fun a j => Real.log (8 * Real.pi * a j) + W j
  let additiveResidual : (ℕ → ℝ) → ℕ → ℝ :=
    fun a j => 4 * (j : ℝ) * a j - W j
  let logarithmicGauge : (ℕ → ℝ) → ℕ → ℝ :=
    fun a j => Real.log (j : ℝ) * R a j
  (Asymptotics.IsEquivalent Filter.atTop W (fun j : ℕ => Real.log (j : ℝ))) ∧
    (∀ a : ℕ → ℝ, (∀ j, 0 < a j) →
      (Filter.Tendsto (fun j => additiveResidual a j) Filter.atTop (nhds 0) ↔
        Filter.Tendsto (fun j => W j * R a j) Filter.atTop (nhds 0))) ∧
    (∃ a : ℕ → ℝ,
      (∀ j, 0 < a j) ∧
      Filter.Tendsto (fun j => R a j) Filter.atTop (nhds 0) ∧
      ¬ Filter.Tendsto (fun j => additiveResidual a j) Filter.atTop (nhds 0)) ∧
    (∀ a : ℕ → ℝ, (∀ j, 0 < a j) →
      (Filter.Tendsto (fun j => additiveResidual a j) Filter.atTop (nhds 0) ↔
        Filter.Tendsto (fun j => logarithmicGauge a j) Filter.atTop (nhds 0)))

end MathlibPlus.Open.Analysis
