import Mathlib

namespace MathlibPlus.Analysis.Schoenberg

noncomputable section

/-- The forbidden-sector angle from the admitted claim. The denominator is
interpreted in `ℝ`, so the displayed `N + m - 1` is real subtraction rather than
natural-number truncation. -/
def forbiddenSectorAngle (N m : ℕ) : ℝ :=
  Real.pi * (m : ℝ) / ((N : ℝ) + (m : ℝ) - 1)

theorem forbiddenSectorAngle_eq (N m : ℕ) :
    forbiddenSectorAngle N m =
      Real.pi * (m : ℝ) / ((N : ℝ) + (m : ℝ) - 1) := by
  rfl

theorem forbiddenSectorAngle_pos {N m : ℕ} (hN : 1 ≤ N) (hm : 0 < m) :
    0 < forbiddenSectorAngle N m := by
  dsimp [forbiddenSectorAngle]
  have hden : 0 < (N : ℝ) + (m : ℝ) - 1 := by
    have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  positivity

end

end MathlibPlus.Analysis.Schoenberg
