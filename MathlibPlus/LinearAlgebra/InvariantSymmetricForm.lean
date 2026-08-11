import Mathlib

namespace MathlibPlus.LinearAlgebra

noncomputable section

theorem reciprocalBlock_invariant_classification (a b c : ℝ)
    (hInv :
      (let H : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]
       let U : Matrix (Fin 2) (Fin 2) ℝ := !![(2 : ℝ), 0; 0, (1 / 2 : ℝ)]
       U.transpose * H * U = H)) :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]
    a = 0 ∧ c = 0 ∧ (Matrix.det H ≠ 0 ↔ b ≠ 0) ∧
      (b ≠ 0 → Matrix.det H < 0) ∧ ¬ H.PosDef := by
  dsimp at hInv ⊢
  have h00 := congrFun (congrFun hInv 0) 0
  have h11 := congrFun (congrFun hInv 1) 1
  have ha : 2 * a * 2 = a := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
  have hc : (2 : ℝ)⁻¹ * c * (2 : ℝ)⁻¹ = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
  have ha0 : a = 0 := by nlinarith [ha]
  have hc0 : c = 0 := by
    norm_num at hc ⊢
    nlinarith [hc]
  refine ⟨ha0, hc0, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two, ha0, hc0]
  · simp [Matrix.det_fin_two, ha0, hc0]
  · intro hPos
    have hplus := hPos.dotProduct_mulVec_pos (x := ![(1 : ℝ), 1]) (by norm_num)
    have hminus := hPos.dotProduct_mulVec_pos (x := ![(1 : ℝ), -1]) (by norm_num)
    simp [Matrix.mulVec, dotProduct, ha0, hc0] at hplus hminus
    linarith

end

end MathlibPlus.LinearAlgebra
