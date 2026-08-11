import Mathlib

namespace MathlibPlus.Analysis

open scoped BigOperators

noncomputable section

/--
The determinant fragment of admitted claim 10470.  For a finite prime
carrier, the inverse determinant of `1 - T` is the finite twisted Euler
product.  The character and spectral parameter are left as the source states
them; no extra Dirichlet hypotheses are introduced.
-/
theorem finitePrimeLocalCarrier_determinant_10470
    (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime) (χ : ℕ → ℂ) (s : ℂ) :
    let ι := {p : ℕ // p ∈ S}
    let w : ℕ → ℂ := fun p =>
      χ p * Complex.exp (-s * (Real.log (p : ℝ) : ℂ))
    let T : Matrix ι ι ℂ := Matrix.diagonal (fun p => w p.1)
    (Matrix.det (1 - T))⁻¹ = ∏ p ∈ S, (1 - w p)⁻¹ := by
  dsimp
  classical
  have hdet : Matrix.det (1 - Matrix.diagonal (fun p : {p : ℕ // p ∈ S} =>
      χ p.1 * Complex.exp (-s * (Real.log (p.1 : ℝ) : ℂ)))) =
      ∏ p ∈ S, (1 - χ p * Complex.exp (-s * (Real.log (p : ℝ) : ℂ))) := by
    rw [show (1 - Matrix.diagonal (fun p : {p : ℕ // p ∈ S} =>
        χ p.1 * Complex.exp (-s * (Real.log (p.1 : ℝ) : ℂ)))) =
        Matrix.diagonal (fun p : {p : ℕ // p ∈ S} =>
          1 - χ p.1 * Complex.exp (-s * (Real.log (p.1 : ℝ) : ℂ))) by
      ext i j
      by_cases h : i = j
      · subst h
        simp
      · simp [h]]
    rw [Matrix.det_diagonal]
    exact (Finset.prod_subtype S (fun _ => Iff.rfl)
      (fun p => 1 - χ p * Complex.exp (-s * (Real.log (p : ℝ) : ℂ)))).symm
  rw [hdet]
  rw [Finset.prod_inv_distrib]

/--
The power-trace fragment of admitted claim 10470.  This is the exact
prime-power identity for every positive or zero power (the source's useful
case is `m > 0`).
-/
theorem finitePrimeLocalCarrier_trace_10470
    (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime) (χ : ℕ → ℂ) (s : ℂ) (m : ℕ) :
    let ι := {p : ℕ // p ∈ S}
    let w : ℕ → ℂ := fun p =>
      χ p * Complex.exp (-s * (Real.log (p : ℝ) : ℂ))
    let T : Matrix ι ι ℂ := Matrix.diagonal (fun p => w p.1)
    Matrix.trace (T ^ m) = ∑ p ∈ S, (w p) ^ m := by
  dsimp
  classical
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  exact (Finset.sum_subtype S (fun _ => Iff.rfl)
    (fun p => (χ p * Complex.exp (-s * (Real.log (p : ℝ) : ℂ))) ^ m)).symm

end
end MathlibPlus.Analysis
