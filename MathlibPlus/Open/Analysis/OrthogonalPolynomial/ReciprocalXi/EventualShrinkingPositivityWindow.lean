import Mathlib

/-!
# Eventual shrinking positivity window for reciprocal xi

Statement-fidelity formalization of admitted claim 486. The reciprocal-xi transform,
its confluent determinant, and the Jacobi coefficients of the normalized reciprocal
weight are inlined so that the window and its scale refer to the intended objects.
-/

open Filter MeasureTheory Matrix Topology

namespace MathlibPlus.Open.Analysis.OrthogonalPolynomial.ReciprocalXi

/-- For each fixed `U > 0`, the reciprocal-xi confluent determinant is eventually
positive throughout `|t| ≤ U / bₙ`; the reciprocal Jacobi scale has both displayed
Lambert-W and logarithmic asymptotic equivalents. -/
def eventualShrinkingPositivityWindow : Prop :=
  let ξ : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let ξr : ℝ → ℝ := fun x => (ξ ((1 / 2 : ℂ) + (x : ℂ))).re
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) /
      ξ ((1 / 2 : ℂ) + (x : ℂ))
  let H : ℕ → ℝ → ℂ := fun n t =>
    (-1 : ℂ) ^ (n * (n - 1) / 2) *
      Matrix.det (fun i j : Fin n => iteratedDeriv (i.val + j.val) F t)
  ∃ (Z : ℝ) (μ : Measure ℝ) (p : ℕ → Polynomial ℝ)
      (b : ℕ → ℝ) (W₀ : ℝ → ℝ),
    (∀ x : ℝ, 0 < ξr x) ∧
    0 < Z ∧
    Z = ∫ x : ℝ, 1 / ξr x ∧
    μ = Measure.withDensity volume
      (fun x => ENNReal.ofReal (1 / (Z * ξr x))) ∧
    (∀ m n : ℕ,
      ∫ x : ℝ, (p m).eval x * (p n).eval x ∂μ = if m = n then 1 else 0) ∧
    (∀ n : ℕ, (p n).natDegree = n ∧ 0 < (p n).leadingCoeff) ∧
    Polynomial.X * p 0 = Polynomial.C (b 1) * p 1 ∧
    (∀ n : ℕ,
      Polynomial.X * p (n + 1) =
        Polynomial.C (b (n + 2)) * p (n + 2) +
          Polynomial.C (b (n + 1)) * p n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < b n) ∧
    (∀ x : ℝ, 0 ≤ x →
      0 ≤ W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) ∧
    (∀ U : ℝ, 0 < U → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t : ℝ,
      |t| ≤ U / b n → (H n t).im = 0 ∧ 0 < (H n t).re) ∧
    Tendsto
      (fun n : ℕ =>
        (1 / b n) /
          (W₀ (2 * (n : ℝ) / Real.exp 1) / (Real.pi * (n : ℝ))))
      atTop (𝓝 1) ∧
    Tendsto
      (fun n : ℕ =>
        (W₀ (2 * (n : ℝ) / Real.exp 1) / (Real.pi * (n : ℝ))) /
          (Real.log (n : ℝ) / (Real.pi * (n : ℝ))))
      atTop (𝓝 1)

end MathlibPlus.Open.Analysis.OrthogonalPolynomial.ReciprocalXi
