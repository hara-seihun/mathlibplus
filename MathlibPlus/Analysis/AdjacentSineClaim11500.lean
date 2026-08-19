import Mathlib

namespace MathlibPlus.Analysis.AdjacentSine

/-- Claim 11500: adjacent degrees cannot both suppress the sine of a fixed phase. -/
theorem adjacentSineLowerBound (θ : ℝ) (d : ℕ) :
    max |Real.sin ((d : ℝ) * θ)| |Real.sin ((d + 1 : ℕ) * θ)| ≥
      |Real.sin θ| / 2 := by
  have hdiff :
      Real.sin θ =
        Real.sin (((d + 1 : ℕ) : ℝ) * θ) * Real.cos ((d : ℝ) * θ) -
          Real.cos (((d + 1 : ℕ) : ℝ) * θ) * Real.sin ((d : ℝ) * θ) := by
    have harg : (((d + 1 : ℕ) : ℝ) * θ - (d : ℝ) * θ) = θ := by
      norm_num
      ring
    calc
      Real.sin θ = Real.sin ((((d + 1 : ℕ) : ℝ) * θ) - (d : ℝ) * θ) := by rw [harg]
      _ = Real.sin (((d + 1 : ℕ) : ℝ) * θ) * Real.cos ((d : ℝ) * θ) -
          Real.cos (((d + 1 : ℕ) : ℝ) * θ) * Real.sin ((d : ℝ) * θ) := by
        rw [Real.sin_sub]
  have hbound : |Real.sin θ| ≤
      |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| + |Real.sin ((d : ℝ) * θ)| := by
    rw [hdiff]
    calc
      |Real.sin (((d + 1 : ℕ) : ℝ) * θ) * Real.cos ((d : ℝ) * θ) -
          Real.cos (((d + 1 : ℕ) : ℝ) * θ) * Real.sin ((d : ℝ) * θ)| ≤
          |Real.sin (((d + 1 : ℕ) : ℝ) * θ) * Real.cos ((d : ℝ) * θ)| +
            |Real.cos (((d + 1 : ℕ) : ℝ) * θ) * Real.sin ((d : ℝ) * θ)| :=
        abs_sub _ _
      _ = |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| *
            |Real.cos ((d : ℝ) * θ)| +
          |Real.cos (((d + 1 : ℕ) : ℝ) * θ)| *
            |Real.sin ((d : ℝ) * θ)| := by rw [abs_mul, abs_mul]
      _ ≤ |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| * 1 +
          1 * |Real.sin ((d : ℝ) * θ)| := by
        gcongr
        · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
        · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
      _ = |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| +
          |Real.sin ((d : ℝ) * θ)| := by ring
  have hmax1 : |Real.sin ((d : ℝ) * θ)| ≤
      max |Real.sin ((d : ℝ) * θ)| |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| :=
    le_max_left _ _
  have hmax2 : |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| ≤
      max |Real.sin ((d : ℝ) * θ)| |Real.sin (((d + 1 : ℕ) : ℝ) * θ)| :=
    le_max_right _ _
  linarith

end MathlibPlus.Analysis.AdjacentSine
