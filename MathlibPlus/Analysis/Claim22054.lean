import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim22054

/--
The displayed transfer estimates follow from the two carrier identities and the
three coefficient bounds.  The equations for `P0R` and `P1R` are kept as
hypotheses because the source packet does not define the underlying operators.
-/
theorem additive_transfer_inequalities
    (P0R P1R R R' R'' p p₀ b b₀ c c₀ : ℝ)
    (hP0 : P0R = R'' + 4 * p * R' + 2 * c * R)
    (hP1 : P1R = R'' + 2 * b * R)
    (hp : |p| ≤ p₀) (hb : |b| ≤ b₀) (hc : |c| ≤ c₀) :
    |P0R| ≤ |R''| + 4 * p₀ * |R'| + 2 * c₀ * |R| ∧
      |P1R| ≤ |R''| + 2 * b₀ * |R| := by
  have hp0 : 0 ≤ p₀ := le_trans (abs_nonneg p) hp
  have hb0 : 0 ≤ b₀ := le_trans (abs_nonneg b) hb
  have hc0 : 0 ≤ c₀ := le_trans (abs_nonneg c) hc
  constructor
  · rw [hP0]
    calc
      |R'' + 4 * p * R' + 2 * c * R| ≤
          |R''| + |4 * p * R'| + |2 * c * R| := by
            calc
              |R'' + 4 * p * R' + 2 * c * R| ≤
                  |R'' + 4 * p * R'| + |2 * c * R| := abs_add_le _ _
              _ ≤ |R''| + |4 * p * R'| + |2 * c * R| := by
                gcongr
                exact abs_add_le _ _
      _ = |R''| + 4 * |p| * |R'| + 2 * |c| * |R| := by
            rw [abs_mul, abs_mul, abs_mul]
            norm_num
      _ ≤ |R''| + 4 * p₀ * |R'| + 2 * c₀ * |R| := by
            gcongr
  · rw [hP1]
    calc
      |R'' + 2 * b * R| ≤ |R''| + |2 * b * R| := abs_add_le _ _
      _ = |R''| + 2 * |b| * |R| := by
            rw [abs_mul, abs_mul]
            norm_num
      _ ≤ |R''| + 2 * b₀ * |R| := by
            gcongr

end MathlibPlus.Analysis.Claim22054
