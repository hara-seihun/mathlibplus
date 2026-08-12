import Mathlib

open Filter MeasureTheory Topology

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/--
For the Jacobi coefficients of the reciprocal completed-xi weight,
`bₙ log n / n` tends to `π`, as asserted in admitted claim 471.

The completed xi normalization and the orthonormal-polynomial recurrence are
inlined because their reusable declarations are still pending admission.
-/
def logarithmicJacobiLimit : Prop :=
  let xi : ℝ → ℝ := fun x =>
    let s : ℂ := (x : ℂ) + 1 / 2
    ((1 + s * (s - 1) * completedRiemannZeta₀ s) / 2).re
  let Q : ℝ → ℝ := fun x => Real.log (xi x)
  ∃ (Z : ℝ) (μ : Measure ℝ) (p : ℕ → Polynomial ℝ) (b : ℕ → ℝ),
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
    Tendsto (fun n : ℕ => b n * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 Real.pi)

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
