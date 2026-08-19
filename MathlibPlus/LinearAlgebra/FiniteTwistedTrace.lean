import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 11669: on a finite set of distinct primes, the diagonal model has
no mixed-prime terms in the logarithmically weighted power trace, and its
finite inverse determinant factors prime by prime. -/
theorem finiteTwistedTraceAndDeterminant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (_hp : ∀ i, Nat.Prime (p i))
    (_hinj : Function.Injective p) (χ : ℕ → ℂ) (s : ℂ)
    (w : ι → ℂ)
    (hw : ∀ i, w i = χ (p i) * (p i : ℂ) ^ (-s)) (k : ℕ) :
    (∑ i, Complex.log (p i : ℂ) *
        ((Matrix.diagonal w) ^ k) i i =
      ∑ i, Complex.log (p i : ℂ) *
        (χ (p i) * (p i : ℂ) ^ (-s)) ^ k) ∧
      (Matrix.det (1 - Matrix.diagonal w))⁻¹ =
        ∏ i, (1 - χ (p i) * (p i : ℂ) ^ (-s))⁻¹ := by
  constructor
  · rw [Matrix.diagonal_pow]
    simp only [Matrix.diagonal_apply_eq, Pi.pow_apply]
    simp_rw [hw]
  · have hdiag : (1 - Matrix.diagonal w : Matrix ι ι ℂ) =
        Matrix.diagonal (fun i => 1 - w i) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    rw [hdiag, Matrix.det_diagonal]
    simp_rw [hw]
    rw [Finset.prod_inv_distrib]

end MathlibPlus.LinearAlgebra
