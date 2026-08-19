import Mathlib

namespace MathlibPlus.LinearAlgebra.PauliSquares

/-- Claim 11827: the explicit arithmetic Pauli frame, its Frobenius
orthogonality, and its multiplication table. -/
theorem arithmeticPauliFrame :
    let Id : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
    let iY : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • Y
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    (∀ (a₀ a₁ a₂ a₃ : ℂ),
      a₀ • Id + a₁ • X + a₂ • iY + a₃ • Z = 0 →
        a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0) ∧
      (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
        ∃ (a₀ a₁ a₂ a₃ : ℂ),
          A = a₀ • Id + a₁ • X + a₂ • iY + a₃ • Z) ∧
      Matrix.trace (Id.transpose * X) = 0 ∧
      Matrix.trace (Id.transpose * iY) = 0 ∧
      Matrix.trace (Id.transpose * Z) = 0 ∧
      Matrix.trace (X.transpose * iY) = 0 ∧
      Matrix.trace (X.transpose * Z) = 0 ∧
      Matrix.trace (iY.transpose * Z) = 0 ∧
      X * X = 1 ∧
      Z * Z = 1 ∧
      iY * iY = -1 ∧
      Z * X = iY ∧
      X * Z = -iY ∧
      Z * X - X * Z = (2 : ℂ) • iY := by
  dsimp
  constructor
  · intro a₀ a₁ a₂ a₃ h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) h
    have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 0) h
    have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) h
    simp [Matrix.add_apply, Matrix.smul_apply] at h00 h01 h10 h11
    constructor
    · linear_combination (h00 + h11) / 2
    constructor
    · linear_combination (h01 + h10) / 2
    constructor
    · linear_combination (h01 - h10) / 2
    · linear_combination (h00 - h11) / 2
  constructor
  · intro A
    refine ⟨(A 0 0 + A 1 1) / 2, (A 0 1 + A 1 0) / 2,
      (A 0 1 - A 1 0) / 2, (A 0 0 - A 1 1) / 2, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply] <;> ring
  constructor
  · simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  constructor
  · simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.smul_apply]
  constructor
  · simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  constructor
  · simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.smul_apply]
  constructor
  · simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  constructor
  · simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
      Matrix.smul_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

end MathlibPlus.LinearAlgebra.PauliSquares
