import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0112

noncomputable def complexPrimePower (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

noncomputable def finiteEulerOperator
    (S : Finset ℕ) (s : ℂ) : Matrix (↥S) (↥S) ℂ :=
  Matrix.diagonal (fun p : ↥S => complexPrimePower p.1 s)

noncomputable def finiteEulerLogSeries (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ S, ∑' m : ℕ,
    complexPrimePower p s ^ (m + 1) / ((m + 1 : ℕ) : ℂ)

noncomputable def finiteEulerAnalyticLog (S : Finset ℕ) (s : ℂ) : ℂ :=
  -finiteEulerLogSeries S s

noncomputable def finiteEulerLogDerivative (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ S, ∑' m : ℕ,
    (Real.log (p : ℝ) : ℂ) * complexPrimePower p s ^ (m + 1)

/-- The exact finite Euler determinant, its convergent analytic logarithm
branch on `Re s > 0`, its logarithm series, and its complex derivative. -/
def claim12226 : Prop :=
  ∀ (S : Finset ℕ),
    (∀ p ∈ S, Nat.Prime p) →
      (∀ s : ℂ,
        Matrix.det (1 - finiteEulerOperator S s) =
          ∏ p ∈ S, (1 - complexPrimePower p s)) ∧
      DifferentiableOn ℂ (finiteEulerAnalyticLog S)
        {s : ℂ | 0 < s.re} ∧
      ∀ s : ℂ, 0 < s.re →
        let P_s := finiteEulerOperator S s
        let determinant : ℂ := Matrix.det (1 - P_s)
        let analyticLog : ℂ := finiteEulerAnalyticLog S s
        let series : ℂ := finiteEulerLogSeries S s
        let derivative : ℂ := finiteEulerLogDerivative S s
        determinant = ∏ p ∈ S, (1 - complexPrimePower p s) ∧
          Complex.exp analyticLog = determinant ∧
          -analyticLog = series ∧
          deriv (finiteEulerAnalyticLog S) s = derivative

end MathlibPlus.Open.ResearchFormalization.BatchO0112
