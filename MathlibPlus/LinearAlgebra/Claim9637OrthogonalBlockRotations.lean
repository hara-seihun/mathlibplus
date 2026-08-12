import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.LinearAlgebra

/--
A block-diagonal family of real two-dimensional sine-cosine rotation blocks is
orthogonal at every choice of the block parameters. The matrix indices are
`Fin 2 × ι`, so the second coordinate records the block.
-/
theorem claim9637_blockDiagonalRotation_isOrthogonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (θ : ι → ℝ) :
    let R : ι → Matrix (Fin 2) (Fin 2) ℝ :=
      fun i => !![Real.cos (θ i), -Real.sin (θ i);
                  Real.sin (θ i), Real.cos (θ i)]
    (Matrix.blockDiagonal R)ᵀ * Matrix.blockDiagonal R = 1 := by
  dsimp
  rw [Matrix.blockDiagonal_transpose]
  rw [← Matrix.blockDiagonal_mul]
  ext ⟨i, k⟩ ⟨j, l⟩
  by_cases hkl : k = l
  · subst l
    simp only [Matrix.blockDiagonal_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      nlinarith [Real.cos_sq_add_sin_sq (θ k)]
  · simp [Matrix.blockDiagonal_apply, hkl]

end MathlibPlus.LinearAlgebra
