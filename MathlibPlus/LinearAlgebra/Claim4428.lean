import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4428

open scoped BigOperators

/-- Factorization of the inverse-Vandermonde moment matrix.  The entry
hypothesis spells out the indexing convention for `P_r`: its `(i,j)` entry is
`∑ p, c p * x p ^ (r - i + j)`. -/
theorem inverseVandermonde_factorization
    {R : Type*} [Field R] {q r : ℕ}
    (hr : q - 1 ≤ r)
    (x c : Fin q → R)
    (hx : ∀ p, x p ≠ 0)
    (P : Matrix (Fin q) (Fin q) R)
    (hP : ∀ i j, P i j = ∑ p : Fin q, c p * x p ^ (r - (i : ℕ) + (j : ℕ))) :
    P =
      (Matrix.transpose (Matrix.vandermonde (fun p => (x p)⁻¹)) *
        Matrix.diagonal (fun p => c p * x p ^ r)) *
          Matrix.vandermonde x := by
  classical
  ext i j
  rw [hP]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro p hp
  simp [Matrix.diagonal, Matrix.vandermonde_apply]
  have hi : (i : ℕ) < q := i.isLt
  have hir : (i : ℕ) ≤ r := by omega
  rw [pow_add, pow_sub₀ (x p) (hx p) hir]
  ring

end MathlibPlus.LinearAlgebra.Claim4428
