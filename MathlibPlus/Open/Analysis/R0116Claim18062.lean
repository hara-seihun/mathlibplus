import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.R0116

/-- Claim 18062: the moments of the explicitly specified shape-`5/4`,
rate-one log-gamma law form an Appell sequence. -/
noncomputable def gammaMomentAppellDerivative_18062 : Prop :=
  let a : ℝ := (5 : ℝ) / 4
  let μ : Measure ℝ :=
    Measure.withDensity volume (fun x : ℝ =>
      ENNReal.ofReal
        (if 0 < x then
          Real.rpow x (a - 1) * Real.exp (-x) / Real.Gamma a
        else 0))
  ∀ (n : ℕ), 1 ≤ n → ∀ y : ℝ,
    deriv (fun y' : ℝ =>
      ∫ x : ℝ, (y' + (1 / 2 : ℝ) * Real.log (Real.pi / x)) ^ n ∂μ) y =
      (n : ℝ) *
        (∫ x : ℝ,
          (y + (1 / 2 : ℝ) * Real.log (Real.pi / x)) ^ (n - 1) ∂μ)

end MathlibPlus.Open.Analysis.R0116
