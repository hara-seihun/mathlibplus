import Mathlib

open Matrix

namespace MathlibPlus.LinearAlgebra.Claim10432

/-- The explicit projection and nilpotent matrix in claim 10432 do not commute. -/
theorem explicit_projection_commutator_ne_zero :
    let L : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    let P : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
    P * L - L * P ≠ 0 := by
  dsimp
  intro h
  have h10 := congrFun (congrFun h 1) 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h10

/-- The first-coordinate line is not invariant under the displayed `L`. -/
theorem first_coordinate_line_not_invariant :
    let L : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    ¬ ∀ v : Fin 2 → ℝ, v 1 = 0 → (L *ᵥ v) 1 = 0 := by
  dsimp
  intro h
  have h_e₀ := h ![1, 0] (by simp)
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h_e₀

end MathlibPlus.LinearAlgebra.Claim10432
