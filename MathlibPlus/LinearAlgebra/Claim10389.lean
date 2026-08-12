import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim10389

noncomputable section

/-- The reciprocal diagonal block preserves the standard alternating form. -/
theorem reciprocalBlock_symplectic_invariant (r : ℝ) (hr : 0 < r) :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![r, 0; 0, r⁻¹]
    let J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]
    U.transpose * J * U = J := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hr.ne']

/-- For a nontrivial positive reciprocal block, invariant symmetric forms have
zero diagonal and are therefore split when nondegenerate. -/
theorem reciprocalBlock_invariant_symmetric (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1)
    (a b c : ℝ)
    (hInv :
      (let H : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]
       let U : Matrix (Fin 2) (Fin 2) ℝ := !![r, 0; 0, r⁻¹]
       U.transpose * H * U = H)) :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, c]
    a = 0 ∧ c = 0 ∧
      Matrix.det H = -b ^ 2 ∧
      (Matrix.det H ≠ 0 ↔ b ≠ 0) ∧
      (b ≠ 0 → ¬ H.PosDef) := by
  dsimp at hInv ⊢
  have h00 := congrFun (congrFun hInv 0) 0
  have h11 := congrFun (congrFun hInv 1) 1
  have ha : r * a * r = a := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
  have hc : r⁻¹ * c * r⁻¹ = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h11
  have hr2 : r ^ 2 ≠ 1 := by
    intro h
    have hfactor : (r - 1) * (r + 1) = 0 := by
      nlinarith [h]
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · exact hr1 (by linarith)
    · linarith
  have ha0 : a = 0 := by
    have ha' : (r ^ 2 - 1) * a = 0 := by
      nlinarith [ha]
    rcases mul_eq_zero.mp ha' with h | h
    · exfalso
      apply hr2
      nlinarith
    · exact h
  have hrInv : r⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hr)
  have hrInv1 : r⁻¹ ^ 2 ≠ 1 := by
    intro h
    have : r ^ 2 = 1 := by
      field_simp at h ⊢
      nlinarith [h]
    exact hr2 this
  have hc0 : c = 0 := by
    have hc' : (r⁻¹ ^ 2 - 1) * c = 0 := by
      nlinarith [hc]
    rcases mul_eq_zero.mp hc' with h | h
    · exfalso
      apply hrInv1
      linarith
    · linarith
  refine ⟨ha0, hc0, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_two, ha0, hc0]
    ring
  · simp [Matrix.det_fin_two, ha0, hc0]
  · intro hb hPos
    have hplus := hPos.dotProduct_mulVec_pos (x := ![(1 : ℝ), 1]) (by norm_num)
    have hminus := hPos.dotProduct_mulVec_pos (x := ![(1 : ℝ), -1]) (by norm_num)
    simp [Matrix.mulVec, dotProduct, ha0, hc0] at hplus hminus
    linarith

end

end MathlibPlus.LinearAlgebra.Claim10389
