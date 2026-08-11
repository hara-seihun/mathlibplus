import Mathlib

/-!
# Reciprocal-xi transform and confluent determinant

This file formalizes the two defining identities in admitted claim 488.  The
pole-removed completed zeta expression is used for the entire Riemann xi function,
so its values at `0` and `1` are not artifacts of division by a totalized pole.
-/

open MeasureTheory

namespace MathlibPlus.Analysis.ReciprocalXi

/-- The reciprocal-xi Fourier transform and every oriented confluent determinant
are the functions given by the displayed integral and derivative-determinant
formulas of admitted claim 488. -/
theorem transformAndConfluentDeterminant :
    let ξ : ℂ → ℂ := fun s =>
      (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
    let F : ℝ → ℂ := fun t =>
      ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) /
        ξ ((1 / 2 : ℂ) + (x : ℂ))
    let H : ℕ → ℝ → ℂ := fun n t =>
      (-1 : ℂ) ^ (n * (n - 1) / 2) *
        Matrix.det (fun j k : Fin n => iteratedDeriv (j.val + k.val) F t)
    (∀ t : ℝ,
      F t = ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) /
        ξ ((1 / 2 : ℂ) + (x : ℂ))) ∧
      ∀ (n : ℕ) (t : ℝ),
        H n t = (-1 : ℂ) ^ (n * (n - 1) / 2) *
          Matrix.det (fun j k : Fin n => iteratedDeriv (j.val + k.val) F t) := by
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩

end MathlibPlus.Analysis.ReciprocalXi
