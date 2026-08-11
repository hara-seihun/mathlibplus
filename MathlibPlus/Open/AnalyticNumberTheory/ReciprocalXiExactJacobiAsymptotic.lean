import Mathlib

open Filter MeasureTheory Topology

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/--
The reciprocal-completed-xi Jacobi coefficients have both Lambert-W asymptotic
equivalents asserted in admitted claim 470, including the `7/8` shift.

`W₀` is characterized as the nonnegative real inverse of `w ↦ w exp w` on the
nonnegative axis. The completed xi function and canonical Jacobi data are inlined.
-/
def exactJacobiCoefficientAsymptotic : Prop :=
  let xi : ℝ → ℝ := fun x =>
    let s : ℂ := (x : ℂ) + 1 / 2
    ((1 + s * (s - 1) * completedRiemannZeta₀ s) / 2).re
  let Q : ℝ → ℝ := fun x => Real.log (xi x)
  ∃ (W₀ : ℝ → ℝ) (Z : ℝ) (μ : Measure ℝ)
      (p : ℕ → Polynomial ℝ) (b : ℕ → ℝ),
    (∀ x : ℝ, 0 ≤ x →
      0 ≤ W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) ∧
    0 < Z ∧
    Z = ∫ x : ℝ, Real.exp (-Q x) ∧
    μ = Measure.withDensity volume
      (fun x => ENNReal.ofReal (Real.exp (-Q x) / Z)) ∧
    (∀ m n : ℕ,
      ∫ x : ℝ, (p m).eval x * (p n).eval x ∂μ = if m = n then 1 else 0) ∧
    (∀ n : ℕ, (p n).natDegree = n) ∧
    Polynomial.X * p 0 = Polynomial.C (b 1) * p 1 ∧
    (∀ n : ℕ,
      Polynomial.X * p (n + 1) =
        Polynomial.C (b (n + 2)) * p (n + 2) +
          Polynomial.C (b (n + 1)) * p n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < b n) ∧
    let shifted : ℕ → ℝ := fun n =>
      Real.pi * ((n : ℝ) - 7 / 8) /
        W₀ (2 * ((n : ℝ) - 7 / 8) / Real.exp 1)
    let leading : ℕ → ℝ := fun n =>
      Real.pi * (n : ℝ) / W₀ (2 * (n : ℝ) / Real.exp 1)
    Tendsto (fun n : ℕ => b n / shifted n) atTop (𝓝 1) ∧
    Tendsto (fun n : ℕ => shifted n / leading n) atTop (𝓝 1)

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
