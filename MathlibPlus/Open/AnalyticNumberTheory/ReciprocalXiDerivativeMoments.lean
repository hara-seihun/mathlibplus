import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/-- At zero, reciprocal-xi Fourier derivatives are the moments times powers of `i`.
The resulting row/column phases give the exact determinant sign, which the oriented
confluent-Hankel prefactor cancels. -/
noncomputable def derivativeMomentSignCancellation : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let X : ℝ → ℝ := fun x =>
    (xi ((1 / 2 : ℂ) + (x : ℂ))).re
  let moment : ℕ → ℝ := fun k =>
    ∫ x : ℝ, x ^ k / X x
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ,
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) / (X x : ℂ)
  let H : ℕ → ℝ → ℂ := fun n t =>
    (-1 : ℂ) ^ (n * (n - 1) / 2) *
      Matrix.det (fun j k : Fin n => iteratedDeriv (j.val + k.val) F t)
  (∀ k : ℕ,
      iteratedDeriv k F 0 = Complex.I ^ k * (moment k : ℂ)) ∧
    (∀ n : ℕ,
      Matrix.det (fun j k : Fin n =>
          iteratedDeriv (j.val + k.val) F 0) =
        (-1 : ℂ) ^ (n * (n - 1) / 2) *
          Matrix.det (fun j k : Fin n => (moment (j.val + k.val) : ℂ))) ∧
    ∀ n : ℕ,
      H n 0 = Matrix.det (fun j k : Fin n =>
        (moment (j.val + k.val) : ℂ))

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
