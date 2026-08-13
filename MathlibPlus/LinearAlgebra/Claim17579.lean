import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17579

/-- The off-diagonal symplectic exchange matrix appearing in the Maslov form. -/
def maslovExchange : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The displayed diagonal-relative-transfer Maslov matrix, with the source
Maslov-transform convention left explicit for fidelity review. -/
theorem displayedMaslovDiagonalForm (R : ℝ) (_hR : R + 1 ≠ 0) :
    let τ : ℝ := (R - 1) / (R + 1)
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      !![0, -τ; -τ, 0]
    M = -τ • maslovExchange := by
  dsimp [maslovExchange]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end MathlibPlus.LinearAlgebra.Claim17579
