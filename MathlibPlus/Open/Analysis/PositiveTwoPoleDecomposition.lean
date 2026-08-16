import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Claim 12981: positive two-pole decomposition of the one-zero rational factor. -/
def positiveTwoPoleDecomposition : Prop :=
  ∀ (γ t : ℝ), 0 < γ → 0 < t →
    let delta : ℝ := Real.sqrt (γ ^ 4 + 4 * t ^ 2)
    let rPlus : ℂ := (((-γ ^ 2 + delta) / 2 : ℝ) : ℂ)
    let rMinus : ℂ := (((-γ ^ 2 - delta) / 2 : ℝ) : ℂ)
    let aPlus : ℝ := 1 - γ ^ 2 / delta
    let aMinus : ℝ := 1 + γ ^ 2 / delta
    let h : ℂ → ℂ := fun z =>
      (2 : ℂ) * z /
        (z ^ 2 + ((γ ^ 2 : ℝ) : ℂ) * z - ((t ^ 2 : ℝ) : ℂ))
    (∀ r : ℂ,
        (MeromorphicAt h r ∧ ¬ AnalyticAt ℂ h r) ↔
          r = rPlus ∨ r = rMinus) ∧
      (∀ z : ℂ, z ≠ rPlus → z ≠ rMinus →
        h z = (aPlus : ℂ) / (z - rPlus) + (aMinus : ℂ) / (z - rMinus)) ∧
      0 < aPlus ∧ 0 < aMinus ∧
      rPlus.im = 0 ∧ rMinus.im = 0 ∧
      (∀ z : ℂ, 0 < z.im → (h z).im < 0)

end MathlibPlus.Open.Analysis
