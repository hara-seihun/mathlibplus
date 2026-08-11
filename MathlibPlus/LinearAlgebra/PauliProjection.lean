import Mathlib

namespace MathlibPlus.LinearAlgebra.PauliProjection

/-!
# Simultaneous involution projection

The source's coefficient matrices are represented by `2 × 2` complex matrices.
The involution `X` is the coordinate-swap matrix, and the rank-one matrix
`F(τ)F(w)ᵀ` is represented entrywise by `F τ i * F w j`.  Scalar division by
two is written as scalar multiplication by `(1 / 2 : ℂ)`.
-/

/-- Simultaneous conjugation by the coordinate-swap involution projects a
rank-one coefficient matrix to the span of the identity and the involution. -/
theorem simultaneousXConjugation (α : Type*) (F : α → Fin 2 → ℂ) (τ w : α) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let K : Matrix (Fin 2) (Fin 2) ℂ := fun i j => F τ i * F w j
    let A : ℂ := Matrix.trace K
    let C : ℂ := Matrix.trace (X * K)
    (1 / 2 : ℂ) • (K + X * K * X) =
      (1 / 2 : ℂ) • (A • (1 : Matrix (Fin 2) (Fin 2) ℂ) + C • X) := by
  dsimp
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  have hproj (K : Matrix (Fin 2) (Fin 2) ℂ) :
      (1 / 2 : ℂ) • (K + X * K * X) =
        (1 / 2 : ℂ) •
          ((Matrix.trace K) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
            (Matrix.trace (X * K)) • X) := by
    have hA : Matrix.trace K = K 0 0 + K 1 1 := Matrix.trace_fin_two K
    have hC : Matrix.trace (X * K) = K 0 1 + K 1 0 := by
      calc
        Matrix.trace (X * K) = (X * K) 0 0 + (X * K) 1 1 := Matrix.trace_fin_two _
        _ = K 0 1 + K 1 0 := by
          simp [X, Matrix.mul_apply, Fin.sum_univ_two]
          ring
    have hX : X * K * X = !![K 1 1, K 1 0; K 0 1, K 0 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [hA, hC, hX]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [X, Matrix.add_apply, Matrix.smul_apply]
    <;> ring
  simpa [X] using hproj (fun i j => F τ i * F w j)

end MathlibPlus.LinearAlgebra.PauliProjection
