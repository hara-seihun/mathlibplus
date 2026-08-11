import Mathlib

open Filter MeasureTheory Topology

namespace MathlibPlus.Open.Analysis.OrthogonalPolynomial.ReciprocalXi

/--
For every fixed compact real interval, the reciprocal-xi confluent determinant,
normalized at zero and evaluated on its exact Jacobi scale, converges uniformly
to the standard Gaussian characteristic function. This is admitted claim 485.
-/
noncomputable def compactUniformGaussianDeterminantLimit : Prop :=
  let xi : ℝ → ℝ := fun x =>
    let s : ℂ := (x : ℂ) + 1 / 2
    ((1 + s * (s - 1) * completedRiemannZeta₀ s) / 2).re
  let Z : ℝ := ∫ x : ℝ, 1 / xi x
  let μ : Measure ℝ := Measure.withDensity volume
    (fun x => ENNReal.ofReal ((1 / xi x) / Z))
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) / (xi x : ℂ)
  let H : ℕ → ℝ → ℂ := fun n t =>
    (-1 : ℂ) ^ (n * (n - 1) / 2) *
      Matrix.det (fun j k : Fin n => iteratedDeriv (j.val + k.val) F t)
  ∃ (p : ℕ → Polynomial ℝ) (b : ℕ → ℝ),
    (∀ n : ℕ, (p n).natDegree = n ∧ 0 < (p n).leadingCoeff) ∧
    (∀ m n : ℕ,
      ∫ x : ℝ, (p m).eval x * (p n).eval x ∂μ = if m = n then 1 else 0) ∧
    Polynomial.X * p 0 = Polynomial.C (b 1) * p 1 ∧
    (∀ n : ℕ, 1 ≤ n →
      Polynomial.X * p n =
        Polynomial.C (b (n + 1)) * p (n + 1) +
          Polynomial.C (b n) * p (n - 1)) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < b n) ∧
    ∀ U : ℝ, 0 < U → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, |u| ≤ U →
        ‖H n (u / b n) / H n 0 -
          (Real.exp (-(u ^ 2) / 2) : ℂ)‖ < ε

end MathlibPlus.Open.Analysis.OrthogonalPolynomial.ReciprocalXi
