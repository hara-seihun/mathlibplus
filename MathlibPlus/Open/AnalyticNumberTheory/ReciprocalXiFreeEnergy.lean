import Mathlib

/-!
# Reciprocal-xi determinant free energy

Statement-fidelity formalization of admitted claim 496.  The reciprocal
Fourier transform and oriented confluent determinant are inlined so that the
asymptotic has no dependency on another pending submission.
-/

open MeasureTheory Matrix Filter Asymptotics

namespace MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi

/-- The reciprocal-xi Hankel determinant has the asserted `n^2` free-energy
expansion.  Positivity at the binding point is explicit, rather than relying
on Lean's totalized real logarithm. -/
noncomputable def determinantFreeEnergy : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let centeredXi : ℂ → ℂ := fun z => xi ((1 / 2 : ℂ) + z)
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) / centeredXi (x : ℂ)
  ∃ H : ℕ → ℝ → ℝ,
    (∀ (n : ℕ) (t : ℝ),
      (H n t : ℂ) =
        (-1 : ℂ) ^ (n * (n - 1) / 2) *
          Matrix.det (fun j k : Fin n => iteratedDeriv (j.val + k.val) F t)) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < H n 0) ∧
    (fun n : ℕ =>
        Real.log (H n 0) -
          (n : ℝ) ^ 2 *
            (Real.log (n : ℝ) - Real.log (Real.log (n : ℝ)) +
              Real.log Real.pi - (3 / 2 : ℝ)))
      =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

end MathlibPlus.Open.AnalyticNumberTheory.ReciprocalXi
