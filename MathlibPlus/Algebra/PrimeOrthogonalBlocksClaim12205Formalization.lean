import Mathlib

namespace MathlibPlus.Algebra.PrimeOrthogonalBlocksClaim12205Formalization

/-- The exact finite diagonal weighted trace in Claim 12205.  The three
functions carry the local values `log p`, `chi p`, and `p^(-s)`. -/
theorem weightedTrace_claim12205 {n : ℕ}
    (logp chi pMinus : Fin n → ℂ) (k : ℕ) :
    Matrix.trace
        (Matrix.diagonal logp *
          (Matrix.diagonal (fun p => chi p * pMinus p)) ^ k) =
      ∑ p : Fin n, logp p * chi p ^ k * pMinus p ^ k := by
  rw [Matrix.diagonal_pow]
  simp [Matrix.trace_diagonal, mul_pow, mul_assoc]

/-- The exact complementary determinant/product identity in Claim 12205. -/
theorem complementaryDeterminant_claim12205 {n : ℕ}
    (chi pMinus : Fin n → ℂ) :
    (Matrix.det
        (1 - Matrix.diagonal (fun p => chi p * pMinus p)))⁻¹ =
      ∏ p : Fin n, (1 - chi p * pMinus p)⁻¹ := by
  have hdiag :
      (1 - Matrix.diagonal (fun p => chi p * pMinus p) :
          Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun p => 1 - chi p * pMinus p) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [hdiag, Matrix.det_diagonal]
  simp

end MathlibPlus.Algebra.PrimeOrthogonalBlocksClaim12205Formalization
