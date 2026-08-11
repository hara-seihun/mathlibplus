import Mathlib

/-!
# Positivity of completed-theta shells
-/

namespace MathlibPlus.Analysis.ThetaShell

/-- Every completed-theta shell is strictly positive on the nonnegative
half-line. The expression is the packet's factored form of `Φₙ`. -/
theorem strictPos (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    0 < 2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      (2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)) := by
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_sq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hexp : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hprod : (1 : ℝ) ≤ (n : ℝ) ^ 2 * Real.exp (2 * u) :=
    one_le_mul_of_one_le_of_one_le hn_sq hexp
  have hpi_prod : 2 * Real.pi ≤
      2 * Real.pi * ((n : ℝ) ^ 2 * Real.exp (2 * u)) := by
    have hnonneg : 0 ≤
        (2 * Real.pi) * ((n : ℝ) ^ 2 * Real.exp (2 * u) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hprod)
    nlinarith
  have hmiddle : 0 <
      2 * Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3 := by
    nlinarith [Real.pi_gt_three]
  positivity

end MathlibPlus.Analysis.ThetaShell
