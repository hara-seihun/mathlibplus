import Mathlib

namespace MathlibPlus.LinearAlgebra

open scoped BigOperators

/-- Right multiplication by a diagonal matrix scales column `j` by `w j`. -/
theorem columnScalingEntry
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) (w : n → R) (i j : n) :
    (M * Matrix.diagonal w) i j = M i j * w j := by
  rw [Matrix.mul_diagonal]

/-- Claim 4961: right multiplication by a diagonal matrix scales the columns
of a square matrix, and the determinant acquires the product of the scalars. -/
theorem columnScalingDeterminant
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) (w : n → R) :
    (M * Matrix.diagonal w).det = M.det * ∏ j, w j := by
  rw [Matrix.det_mul, Matrix.det_diagonal]

/-- Nonzero column weights preserve determinant nonvanishing. -/
theorem columnScalingDeterminantNeZeroIff
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    [NoZeroDivisors R] [Nontrivial R]
    (M : Matrix n n R) (w : n → R) (hw : ∀ j, w j ≠ 0) :
    (M * Matrix.diagonal w).det ≠ 0 ↔ M.det ≠ 0 := by
  rw [columnScalingDeterminant]
  constructor
  · intro h hdet
    apply h
    rw [hdet, zero_mul]
  · intro h
    exact mul_ne_zero h (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hw i))

/-- Nonzero column weights preserve the column rank. -/
theorem columnScalingRank
    {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Field R]
    (M : Matrix n n R) (w : n → R) (hw : ∀ j, w j ≠ 0) :
    (M * Matrix.diagonal w).rank = M.rank := by
  apply Matrix.rank_mul_eq_left_of_det_ne_zero (Matrix.diagonal w) M
  rw [Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hw i)

end MathlibPlus.LinearAlgebra
