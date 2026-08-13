import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim11026

noncomputable section

theorem fourierReflection_sq :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        !![0, 1; -1, 0] = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem fourierReflection_inv :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      - (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.inv_def]
  simp [Matrix.det_fin_two]

theorem hyperbolicBlock_inv (p : ℝ) (hp : p ≠ 0) :
    (!![p⁻¹, 0; 0, p] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![p, 0; 0, p⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ := by
  rw [Matrix.inv_def]
  simp [Matrix.det_fin_two, hp]

theorem fourierReflection_hyperbolicBlock (p : ℝ) (hp : p ≠ 0) :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *
        !![p, 0; 0, p⁻¹] *
        (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ =
      (!![p, 0; 0, p⁻¹] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ := by
  rw [fourierReflection_inv, ← hyperbolicBlock_inv p hp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

end

end MathlibPlus.LinearAlgebra.Claim11026
