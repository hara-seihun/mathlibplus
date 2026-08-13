import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim23222

/-- A complete private-row peeling sequence produces a nonsingular square minor:
the selected rows and columns form an upper-triangular matrix with nonzero
diagonal, so its columns have full rank. This is the kernel-checkable
linear-algebra core of admitted claim 23222. -/
theorem privateRowPeeling_nonsingularMinor_claim23222
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ)
    (rows : Fin n → Fin m) (cols : Fin n → Fin n)
    (_hrows : Function.Injective rows)
    (_hcols : Function.Injective cols)
    (hdiag : ∀ i, M (rows i) (cols i) ≠ 0)
    (hupper : ∀ i j, j < i → M (rows i) (cols j) = 0) :
    let A : Matrix (Fin n) (Fin n) ℚ := fun i j => M (rows i) (cols j)
    A.det ≠ 0 ∧ A.rank = n ∧ LinearIndependent ℚ A.col := by
  let A : Matrix (Fin n) (Fin n) ℚ := fun i j => M (rows i) (cols j)
  change A.det ≠ 0 ∧ A.rank = n ∧ LinearIndependent ℚ A.col
  have hupperA : A.IsUpperTriangular := by
    intro i j hij
    change M (rows i) (cols j) = 0
    exact hupper i j hij
  have hprod : (∏ i : Fin n, A i i) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact hdiag i
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hupperA]
    exact hprod
  refine ⟨hdet, ?_, Matrix.linearIndependent_cols_of_det_ne_zero hdet⟩
  simpa using (Matrix.rank_of_det_ne_zero hdet)

end MathlibPlus.LinearAlgebra.Claim23222
