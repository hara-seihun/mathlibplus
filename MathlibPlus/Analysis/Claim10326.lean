import Mathlib

namespace MathlibPlus.Analysis.Claim10326

/-- A real state lies in every sufficiently small cutoff strip exactly on the
critical line.  This is the form-domain interpretation of claim 10326. -/
theorem shrinking_cutoff_iff (β : ℝ) :
    (∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → |2 * β - 1| < ε) ↔
      β = (1 : ℝ) / 2 := by
  constructor
  · rintro ⟨ε₀, hε₀, hsmall⟩
    by_contra hβ
    have hd : 0 < |2 * β - 1| := by
      have hne : 2 * β - 1 ≠ 0 := by
        intro hzero
        apply hβ
        linarith
      exact abs_pos.mpr hne
    let ε := min (ε₀ / 2) (|2 * β - 1| / 2)
    have hε : 0 < ε := by
      dsimp [ε]
      exact lt_min (by linarith) (by linarith)
    have hεlt : ε < ε₀ := by
      dsimp [ε]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hcut : |2 * β - 1| < ε := hsmall ε hε hεlt
    have hupper : ε ≤ |2 * β - 1| / 2 := by
      dsimp [ε]
      exact min_le_right _ _
    linarith
  · intro hβ
    refine ⟨1, by norm_num, ?_⟩
    intro ε hε hεlt
    rw [hβ]
    norm_num
    exact hε

end MathlibPlus.Analysis.Claim10326
