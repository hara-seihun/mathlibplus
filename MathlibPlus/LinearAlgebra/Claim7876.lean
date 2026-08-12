import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim7876

/-- The two displayed reflections on the standard Pauli frame.  Here `iY` is
represented by the real matrix `[[0,1],[-1,0]]`, the usual `i` times Pauli Y. -/
theorem arithmetic_pauli_frame_reflections :
    let I : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let iY : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
    let s₀ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
      fun B => B.transpose
    let s₁ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
      fun B => X * B
    s₀ I = I ∧ s₀ X = X ∧ s₀ Z = Z ∧ s₀ iY = -iY ∧
      s₁ I = X ∧ s₁ X = I ∧ s₁ Z = -iY ∧ s₁ iY = -Z := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.Claim7876
