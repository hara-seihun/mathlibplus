import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The Lambert-gauge contribution to a terminally normalized row is anchor-free. -/
theorem terminalGaugeAnchorCancellation
    (a W : ℕ → ℝ) (N j : ℕ)
    (ha : ∀ n, 0 < a n) :
    (let aStar : ℕ → ℝ := fun n => Real.exp (-W n) / (8 * Real.pi)
     let R : ℕ → ℝ := fun n => Real.log (a n / aStar n)
     let _D : ℕ → ℝ := fun n => R n - R (n + 1)
     let cN : ℝ := a N
     Real.log (a j / cN) = W N - W j + R j - R N) := by
  dsimp
  have hpi : 0 < (8 : ℝ) * Real.pi := by positivity
  have hstar : ∀ n : ℕ, 0 < Real.exp (-W n) / (8 * Real.pi) := by
    intro n
    exact div_pos (Real.exp_pos _) hpi
  have ha_ratio : ∀ n : ℕ, 0 < a n / (Real.exp (-W n) / (8 * Real.pi)) := by
    intro n
    exact div_pos (ha n) (hstar n)
  rw [Real.log_div (ha j).ne' (ha N).ne']
  rw [Real.log_div (ha j).ne' (hstar j).ne',
    Real.log_div (ha N).ne' (hstar N).ne']
  rw [Real.log_div (Real.exp_pos (-W j)).ne' hpi.ne',
    Real.log_div (Real.exp_pos (-W N)).ne' hpi.ne']
  simp only [Real.log_exp]
  ring

end MathlibPlus.Analysis
