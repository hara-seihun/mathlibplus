import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The first-shell, age-three evaluation from packet R-0264. -/
theorem firstShellAgeThreeEvaluation_claim19306 (lam : ℝ) :
    let α : ℝ := 1 / 4
    let u : ℝ := 3
    let g : ℝ := 1 + u / 2 - 2 * lam * u * Real.exp (2 * u)
    let ell : ℝ := 1 / 2 + g * (α * u ^ 2 / 8 - 1 / 4)
    ell = 37 / 64 - 3 * lam * Real.exp 6 / 16 := by
  norm_num
  ring

end MathlibPlus.Analysis
