import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace MathlibPlus.LinearAlgebra.Claim11106

/-- The two displayed Frobenius squares are distinct and non-scalar. -/
theorem frobeniusSquares_claim11106 :
    let F₁ : Matrix (Fin 2) (Fin 2) ℤ := !![0, -5; 1, -3]
    let F₂ : Matrix (Fin 2) (Fin 2) ℤ := !![0, -5; 1, 4]
    let S₁ : Matrix (Fin 2) (Fin 2) ℤ := !![-5, 15; -3, 4]
    let S₂ : Matrix (Fin 2) (Fin 2) ℤ := !![-5, -20; 4, 11]
    F₁ ^ 2 = S₁ ∧ F₂ ^ 2 = S₂ ∧ S₁ ≠ S₂ ∧
      (¬ ∃ c : ℤ, S₁ = !![c, 0; 0, c]) ∧
      (¬ ∃ c : ℤ, S₂ = !![c, 0; 0, c]) := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    norm_num at h01
  constructor
  · rintro ⟨c, h⟩
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    norm_num at h01
  · rintro ⟨c, h⟩
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) h
    norm_num at h01

end MathlibPlus.LinearAlgebra.Claim11106
