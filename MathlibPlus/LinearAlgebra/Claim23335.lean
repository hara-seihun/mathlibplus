import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim23335

/-- A row supported at one column forces that coordinate to vanish on the
kernel.  This is the abstract linear-algebra content of the private-row
criterion in claim 23335. -/
theorem private_row_kills_kernel_coordinate
    {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n K) (i : m) (G : n)
    (hG : M i G ≠ 0)
    (hzero : ∀ j, j ≠ G → M i j = 0)
    {x : n → K} (hx : M.mulVec x = 0) :
    x G = 0 := by
  have hrow : ∑ j : n, M i j * x j = 0 := by
    simpa [Matrix.mulVec, dotProduct] using congrFun hx i
  have hsum : ∑ j : n, M i j * x j = M i G * x G := by
    classical
    apply Finset.sum_eq_single G
    · intro b _ hne
      rw [hzero b hne, zero_mul]
    · simp
  rw [hsum] at hrow
  exact (mul_eq_zero.mp hrow).resolve_left hG

end MathlibPlus.LinearAlgebra.Claim23335
