import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- The rounded additive subtraction cannot accompany the exact leading
coefficient in the retained logarithmic normalization. -/
def roundedSubtractionCounterfeit_1599 : Prop :=
  let cExact : ℝ := (22077 : ℝ) / 125000
  let cRounded : ℝ := (1767 : ℝ) / 10000
  let b : ℝ := (3161 : ℝ) / 200
  let dRounded : ℝ := b - cRounded * Real.log (2 * Real.pi)
  let dExact : ℝ := b - cExact * Real.log (2 * Real.pi)
  dRounded < dExact ∧
    ¬ ∃ D : ℝ,
      D = dRounded ∧
        ∀ T : ℝ, 1 ≤ T →
          cExact * Real.log (T / (2 * Real.pi)) + b =
            cExact * Real.log T + D

end MathlibPlus.Open.AnalyticNumberTheory
