import Mathlib

/-!
# Reciprocal-xi determinant as an OPE trace characteristic function

Statement-fidelity formalization of admitted claim 484.  The expectation is written
as the normalized `n`-fold Lebesgue integral of the beta-two Vandermonde density, so
that no unformalized probability-law construction is hidden in the notation.
-/

open MeasureTheory

namespace MathlibPlus.Open.Analysis.OrthogonalPolynomial.ReciprocalXi

/-- The reciprocal-xi confluent determinant, normalized at the origin, is the
characteristic function of the trace of the corresponding beta-two orthogonal
polynomial ensemble, for every positive particle number and every real frequency. -/
noncomputable def traceCharacteristicFunction : Prop :=
  let xi : ℂ → ℂ := fun s =>
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2
  let X : ℝ → ℂ := fun x => xi ((1 / 2 : ℂ) + (x : ℂ))
  let w : ℝ → ℝ := fun x => (X x).re⁻¹
  let F : ℝ → ℂ := fun t =>
    ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) / X x
  let H : ℕ → ℝ → ℂ := fun n t =>
    (-1 : ℂ) ^ (n * (n - 1) / 2) *
      Matrix.det (fun i j : Fin n =>
        iteratedDeriv (i.val + j.val) F t)
  let vandermonde : (n : ℕ) → (Fin n → ℝ) → ℝ := fun n x =>
    ∏ i : Fin n, ∏ j : Fin n, if i < j then x j - x i else 1
  let density : (n : ℕ) → (Fin n → ℝ) → ℝ := fun n x =>
    vandermonde n x ^ 2 * ∏ i : Fin n, w (x i)
  let trace : (n : ℕ) → (Fin n → ℝ) → ℝ := fun n x =>
    ∑ i : Fin n, x i
  let partition : ℕ → ℝ := fun n =>
    ∫ x : Fin n → ℝ, density n x
  (∀ n : ℕ, 0 < n → Integrable (density n) ∧ 0 < partition n ∧ H n 0 ≠ 0) ∧
    ∀ n : ℕ, 0 < n → ∀ t : ℝ,
      H n t / H n 0 =
        (∫ x : Fin n → ℝ,
          Complex.exp (Complex.I * ((t * trace n x : ℝ) : ℂ)) *
            (density n x : ℂ)) / (partition n : ℂ)

end MathlibPlus.Open.Analysis.OrthogonalPolynomial.ReciprocalXi
