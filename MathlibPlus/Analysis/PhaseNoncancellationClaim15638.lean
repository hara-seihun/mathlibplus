import MathlibPlus.Analysis.PhaseNoncancellation

namespace MathlibPlus.Analysis.PhaseNoncancellation

/-- Claim 15638: weighting one of two noncancelling cosine phases by at least
one half preserves strict positivity. -/
theorem weightedPhaseNoncancellation (φ θ w : ℝ)
    (hθ : |Real.cos θ| < 1) (hw : 1 / 2 ≤ w) :
    0 < Real.cos φ ^ 2 + w * Real.cos (φ + θ) ^ 2 := by
  have hphase := adjacentPhaseNoncancellation φ θ hθ
  have hsum : 0 < Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2 :=
    lt_of_lt_of_le hphase.2 hphase.1
  have hφ : 0 ≤ Real.cos φ ^ 2 := sq_nonneg _
  have hnext : 0 ≤ Real.cos (φ + θ) ^ 2 := sq_nonneg _
  have hwb : (1 / 2 : ℝ) * Real.cos (φ + θ) ^ 2 ≤
      w * Real.cos (φ + θ) ^ 2 :=
    mul_le_mul_of_nonneg_right hw hnext
  have hbound :
      (1 / 2 : ℝ) * (Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2) ≤
        Real.cos φ ^ 2 + w * Real.cos (φ + θ) ^ 2 := by
    nlinarith
  have hhalf : 0 <
      (1 / 2 : ℝ) * (Real.cos φ ^ 2 + Real.cos (φ + θ) ^ 2) := by
    exact mul_pos (by norm_num) hsum
  exact lt_of_lt_of_le hhalf hbound

end MathlibPlus.Analysis.PhaseNoncancellation
