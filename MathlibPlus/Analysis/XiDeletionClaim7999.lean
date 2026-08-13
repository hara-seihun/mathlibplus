import Mathlib

namespace MathlibPlus.Analysis.XiDeletion

/-- Claim 7999: the displayed deletion factor is positive below the deleted
pole, negative above it, and correspondingly preserves or reverses the sign of
that pole's amplitude. -/
theorem xiDeletionFactor_signs_claim7999
    {γj γm cj : ℝ} (hγj : 0 < γj) (hγm : 0 < γm) :
    let factor := 1 - γj ^ 2 / γm ^ 2
    let cjm := factor * cj
    (γj < γm →
      0 < factor ∧
      ((0 < cj → 0 < cjm) ∧ (cj < 0 → cjm < 0))) ∧
    (γm < γj →
      factor < 0 ∧
      ((0 < cj → cjm < 0) ∧ (cj < 0 → 0 < cjm))) := by
  dsimp
  have hden : 0 < γm ^ 2 := sq_pos_of_pos hγm
  constructor
  · intro hbelow
    have hsq : γj ^ 2 < γm ^ 2 := by
      nlinarith [sq_nonneg (γm - γj), sq_nonneg (γm + γj)]
    have hfactor : 0 < 1 - γj ^ 2 / γm ^ 2 := by
      rw [sub_pos]
      exact (div_lt_iff₀ hden).2 (by simpa using hsq)
    refine ⟨hfactor, ?_⟩
    constructor
    · intro hc
      exact mul_pos hfactor hc
    · intro hc
      exact mul_neg_of_pos_of_neg hfactor hc
  · intro habove
    have hsq : γm ^ 2 < γj ^ 2 := by
      nlinarith [sq_nonneg (γj - γm), sq_nonneg (γj + γm)]
    have hfactor : 1 - γj ^ 2 / γm ^ 2 < 0 := by
      rw [sub_neg]
      exact (lt_div_iff₀ hden).2 (by simpa using hsq)
    refine ⟨hfactor, ?_⟩
    constructor
    · intro hc
      exact mul_neg_of_neg_of_pos hfactor hc
    · intro hc
      exact mul_pos_of_neg_of_neg hfactor hc

end MathlibPlus.Analysis.XiDeletion
