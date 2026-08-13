import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim9531

/-- The Schur-complement pivot for a scalar bottom-right block. -/
theorem schurPivot_claim9531
    {R : Type*} [Field R]
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m R) (b : m → R) (c : R) [Invertible A] :
    let B : Matrix m (Fin 1) R := fun i _ => b i
    let C : Matrix (Fin 1) m R := fun _ j => b j
    let D : Matrix (Fin 1) (Fin 1) R := fun _ _ => c
    (Matrix.fromBlocks A B C D).det =
      A.det * (c - ∑ i, b i * (Matrix.mulVec (⅟ A) b) i) := by
  dsimp
  let B : Matrix m (Fin 1) R := fun i _ => b i
  let C : Matrix (Fin 1) m R := fun _ j => b j
  let D : Matrix (Fin 1) (Fin 1) R := fun _ _ => c
  change (Matrix.fromBlocks A B C D).det = _
  rw [Matrix.det_fromBlocks₁₁ A B C D, Matrix.det_fin_one]
  congr 1
  change c - (C * ⅟ A * B) 0 0 = _
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_apply]
  simp only [B, C, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp [mul_comm, mul_left_comm]

end MathlibPlus.LinearAlgebra.Claim9531
