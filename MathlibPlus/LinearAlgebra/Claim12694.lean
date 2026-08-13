import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim12694

/-- Claim 12694: the characteristic polynomial does not determine the Jordan
structure, witnessed by a scalar matrix and a nontrivial two-by-two Jordan block. -/
theorem determinant_does_not_determine_jordan (lam : ℂ) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![lam, 0; 0, lam]
    let B : Matrix (Fin 2) (Fin 2) ℂ := !![lam, 1; 0, lam]
    A.charpoly = B.charpoly ∧
      ¬ ∃ P : Matrix (Fin 2) (Fin 2) ℂ,
        IsUnit P.det ∧ P * A = B * P := by
  dsimp
  constructor
  · simp [Matrix.charpoly, Matrix.det_fin_two]
  · rintro ⟨P, hP, hconj⟩
    have hdet : P.det = 0 := by
      rw [Matrix.det_fin_two]
      have h00 := congr_fun (congr_fun hconj 0) 0
      have h01 := congr_fun (congr_fun hconj 0) 1
      have h10 := congr_fun (congr_fun hconj 1) 0
      have h11 := congr_fun (congr_fun hconj 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
      norm_num at h00 h01 h10 h11 ⊢
      have hp10 : P 1 0 = 0 := by
        linear_combination (-1) * h00
      have hp11 : P 1 1 = 0 := by
        linear_combination (-1) * h01
      rw [hp10, hp11]
      simp
    exact hP.ne_zero hdet

end MathlibPlus.LinearAlgebra.Claim12694
