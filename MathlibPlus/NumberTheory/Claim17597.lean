import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory.Claim17597

/-- The reciprocal atoms of the affine gamma-wall sequence are positive and strictly decreasing. -/
theorem reciprocal_atoms_pos_strictDecreasing :
    let A : ℕ → ℝ := fun j => ((5 : ℝ) / 2 + 2 * (j : ℝ)) ^ 2
    ∀ j : ℕ, 0 < (A j)⁻¹ ∧ (A (j + 1))⁻¹ < (A j)⁻¹ := by
  dsimp
  intro j
  constructor
  · positivity
  · have hAj : 0 < ((5 : ℝ) / 2 + 2 * (j : ℝ)) ^ 2 := by positivity
    have hAstep : ((5 : ℝ) / 2 + 2 * (j : ℝ)) ^ 2 <
        ((5 : ℝ) / 2 + 2 * ((j + 1 : ℕ) : ℝ)) ^ 2 := by
      have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [hj]
    simpa [one_div] using
      (one_div_lt_one_div_of_lt (α := ℝ) hAj hAstep)

end MathlibPlus.NumberTheory.Claim17597
