import Mathlib

namespace MathlibPlus.Open.Analysis.R0116

/-- Claim 18057: for the shape-`5/4`, rate-one log-gamma variable, the
first cumulant has the displayed digamma value and is strictly positive.
The cumulant is taken from the logarithmic derivative at zero of the exact
moment-generating function in the admitted supporting claim. -/
noncomputable def positiveFirstCumulant_18057 : Prop :=
  let a : ℝ := (5 : ℝ) / 4
  let ψ : ℝ → ℝ := fun x =>
    deriv (fun y : ℝ => Real.log (Real.Gamma y)) x
  let M : ℝ → ℝ := fun t =>
    Real.rpow Real.pi (t / 2) * Real.Gamma (a - t / 2) /
      Real.Gamma a
  let κ₁ : ℝ := deriv (fun t : ℝ => Real.log (M t)) 0
  κ₁ = (1 / 2 : ℝ) * (Real.log Real.pi - ψ a) ∧ 0 < κ₁

end MathlibPlus.Open.Analysis.R0116
