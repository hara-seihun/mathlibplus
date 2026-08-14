import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 51093: the symmetric diagonal affine pencil has no positive-definite
member, despite its central positive block and positive central determinant. -/
theorem terminalConeCounterexample :
    let M : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun δ =>
      Matrix.diagonal ![1 + δ, 1 - δ, -1 + δ / 10, -1 - δ / 10]
    (M 0).det = 1 ∧
    (Matrix.diagonal ![1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧
    (∀ δ : ℝ,
      (M δ).det = 0 ↔
        δ = -10 ∨ δ = -1 ∨ δ = 1 ∨ δ = 10) ∧
    (∀ δ : ℝ,
      (M δ).det = 0 →
        ∃! i : Fin 4,
          (![1 + δ, 1 - δ, -1 + δ / 10, -1 - δ / 10] : Fin 4 → ℝ) i = 0) ∧
    ¬ ∃ δ : ℝ, (M δ).PosDef := by
  dsimp
  have hdet (δ : ℝ) :
      (Matrix.diagonal ![1 + δ, 1 - δ, -1 + δ / 10, -1 - δ / 10] :
        Matrix (Fin 4) (Fin 4) ℝ).det =
        (1 + δ) * (1 - δ) * (-1 + δ / 10) * (-1 - δ / 10) := by
    simp [Matrix.det_diagonal, Fin.prod_univ_succ]
    ring
  have hroot_iff (δ : ℝ) :
      (Matrix.diagonal ![1 + δ, 1 - δ, -1 + δ / 10, -1 - δ / 10] :
        Matrix (Fin 4) (Fin 4) ℝ).det = 0 ↔
        δ = -10 ∨ δ = -1 ∨ δ = 1 ∨ δ = 10 := by
    rw [hdet]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · right
            left
            linarith
          · right
            right
            left
            linarith
        · right
          right
          right
          linarith
      · left
        linarith
    · rintro (rfl | rfl | rfl | rfl) <;> norm_num
  constructor
  · rw [hdet]
    norm_num
  constructor
  · apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  constructor
  · intro δ
    exact hroot_iff δ
  constructor
  · intro δ hroot
    rcases (hroot_iff δ).mp hroot with rfl | rfl | rfl | rfl
    · refine ⟨3, by simp, ?_⟩
      intro i hi
      fin_cases i
      · norm_num at hi
      · norm_num at hi
      · norm_num at hi
      · rfl
    · refine ⟨0, by simp, ?_⟩
      intro i hi
      fin_cases i
      · rfl
      · norm_num at hi
      · norm_num at hi
      · norm_num at hi
    · refine ⟨1, by simp, ?_⟩
      intro i hi
      fin_cases i
      · norm_num at hi
      · rfl
      · norm_num at hi
      · norm_num at hi
    · refine ⟨2, by simp, ?_⟩
      intro i hi
      fin_cases i
      · norm_num at hi
      · norm_num at hi
      · rfl
      · norm_num at hi
  · rintro ⟨δ, hδ⟩
    have hdiag : ∀ i, 0 < (![1 + δ, 1 - δ, -1 + δ / 10, -1 - δ / 10] : Fin 4 → ℝ) i :=
      Matrix.posDef_diagonal_iff.mp hδ
    have h0 := hdiag (0 : Fin 4)
    have h1 := hdiag (1 : Fin 4)
    have h2 := hdiag (2 : Fin 4)
    have h3 := hdiag (3 : Fin 4)
    norm_num at h0 h1 h2 h3
    simp at h2 h3
    linarith

end MathlibPlus.LinearAlgebra
