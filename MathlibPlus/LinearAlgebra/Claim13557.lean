import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim13557

theorem reciprocalFlow_invariantForms_claim13557 :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1 / 2]
    ∀ G : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ i j : Fin 2, G i j = G j i) →
      U.transpose * G * U = G →
      ∃ b : ℝ,
        G = !![0, b; b, 0] ∧
        G.det = -(b ^ 2) ∧
        (G.det ≠ 0 → ¬ G.PosDef) := by
  dsimp
  intro G hsym hinv
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hinv
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hinv
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hinv
  have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hinv
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hG00 : G 0 0 = 0 := by linarith [h00]
  have hG11 : G 1 1 = 0 := by linarith [h11]
  refine ⟨G 0 1, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j
    · exact hG00
    · rfl
    · simpa [hsym 1 0]
    · exact hG11
  · rw [Matrix.det_fin_two]
    norm_num [hG00, hG11, hsym 1 0]
    ring
  · intro hdet hpos
    have hx : ![1, 0] ≠ (0 : Fin 2 → ℝ) := by
      intro h
      have := congrFun h 0
      norm_num at this
    have hquad := hpos.dotProduct_mulVec_pos hx
    norm_num [Matrix.det_fin_two, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, hG00, hG11, hsym 1 0] at hquad

end MathlibPlus.LinearAlgebra.Claim13557
