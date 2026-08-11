import Mathlib

namespace MathlibPlus
namespace Analysis

/-- The displayed `[0,2)` defect matrix is the rank-one signed matrix scaled by
`h₀ h₂ sech² ξ`; `sech ξ` is written as `1 / cosh ξ`. -/
theorem defect_matrix_claim17970 (h₀ h₂ ξ : ℝ) :
    let s : ℝ := (1 / Real.cosh ξ) ^ 2
    (!![h₀ * h₂ * s, -(h₀ * h₂ * s);
        -(h₀ * h₂ * s), h₀ * h₂ * s] : Matrix (Fin 2) (Fin 2) ℝ) =
      (h₀ * h₂ * s) • (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp
  ext i
  fin_cases i <;> simp [Matrix.smul_apply]

end Analysis
end MathlibPlus
