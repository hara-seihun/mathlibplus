import MathlibPlus.Basic

namespace MathlibPlus.LinearAlgebra.Claim10329

/--
Claim 10329.  The off-axis two-state limiting Gram is the symmetric exchange
matrix.  Its real eigenvalues are exactly `1` and `-1`, and its quadratic value
at the vector `(1,-1)` is `-2`.
-/
theorem offAxisTwoStateLimitingGram_claim10329 :
    let G : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
    let v : Fin 2 → ℝ := ![1, -1]
    (∀ eigenvalue : ℝ,
      (∃ w : Fin 2 → ℝ,
        w ≠ 0 ∧ Matrix.mulVec G w = eigenvalue • w) ↔
        eigenvalue = 1 ∨ eigenvalue = -1) ∧
      dotProduct v (Matrix.mulVec G v) = -2 := by
  dsimp
  constructor
  · intro eigenvalue
    constructor
    · rintro ⟨w, hw, heq⟩
      have h0 := congr_fun heq (0 : Fin 2)
      have h1 := congr_fun heq (1 : Fin 2)
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      have hw_cases : w 0 ≠ 0 ∨ w 1 ≠ 0 := by
        by_contra h
        push Not at h
        apply hw
        funext i
        fin_cases i <;> simp [h]
      rcases hw_cases with hwa | hwb
      · have hsquare : eigenvalue ^ 2 = 1 := by
          apply (mul_left_cancel₀ hwa)
          calc
            w 0 * eigenvalue ^ 2 =
                (w 0 * eigenvalue) * eigenvalue := by ring
            _ = w 1 * eigenvalue := by rw [h0]; ring
            _ = w 0 := by rw [h1]; ring
            _ = w 0 * 1 := by ring
        exact (sq_eq_one_iff).mp hsquare
      · have hsquare : eigenvalue ^ 2 = 1 := by
          apply (mul_left_cancel₀ hwb)
          calc
            w 1 * eigenvalue ^ 2 =
                (w 1 * eigenvalue) * eigenvalue := by ring
            _ = w 0 * eigenvalue := by rw [h1]; ring
            _ = w 1 := by rw [h0]; ring
            _ = w 1 * 1 := by ring
        exact (sq_eq_one_iff).mp hsquare
    · intro h
      rcases h with rfl | rfl
      · refine ⟨![1, 1], ?_, ?_⟩
        · intro hzero
          have hzero0 := congr_fun hzero (0 : Fin 2)
          norm_num at hzero0
        · funext i
          fin_cases i <;>
            norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · refine ⟨![1, -1], ?_, ?_⟩
        · intro hzero
          have hzero0 := congr_fun hzero (0 : Fin 2)
          norm_num at hzero0
        · funext i
          fin_cases i <;>
            norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

end MathlibPlus.LinearAlgebra.Claim10329
