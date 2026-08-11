import Mathlib

namespace MathlibPlus.Algebra.PrimeOrthogonalBlocks

/-!
# Prime-orthogonal diagonal blocks

Claim 12691 is independent of arithmetic properties of the labels, so a finite
set of prime labels is represented by `Fin n`.  The two displayed identities
are the precise algebraic content of the absence of mixed-prime terms.
-/

/-- A diagonal prime block has power-trace equal to the sum of its diagonal
entries' powers, and its complementary determinant is the product of the
complementary diagonal entries. -/
theorem primeOrthogonalBlocks {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin n → R) (m : ℕ) :
    let U : Matrix (Fin n) (Fin n) R := Matrix.diagonal x
    Matrix.trace (U ^ m) = ∑ p : Fin n, (x p) ^ m ∧
      Matrix.det (1 - U) = ∏ p : Fin n, (1 - x p) := by
  dsimp
  constructor
  · rw [Matrix.diagonal_pow]
    simp [Matrix.trace_diagonal]
  · have hdiag : (1 - Matrix.diagonal x : Matrix (Fin n) (Fin n) R) =
        Matrix.diagonal (fun p => 1 - x p) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal_apply, h]
    rw [hdiag, Matrix.det_diagonal]

end MathlibPlus.Algebra.PrimeOrthogonalBlocks
