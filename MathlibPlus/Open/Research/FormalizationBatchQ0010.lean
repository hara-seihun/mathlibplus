import Mathlib

namespace MathlibPlus.Open.Research.Q0010

noncomputable def factorialMomentDensity (x : ℝ) : ℝ :=
  (1 - x) / (-Real.log x)

/-- The factorial component as a positive Hausdorff moment contribution. -/
def factorialComponentPositiveMoment : Prop :=
  ∀ n : ℕ,
    2 * Real.log (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) =
      2 * ∫ x : ℝ in Set.Icc 0 1, x ^ n * factorialMomentDensity x ∧
    (∀ x : ℝ, x ∈ Set.Ioo 0 1 → 0 ≤ factorialMomentDensity x) ∧
    0 < ∫ x : ℝ in Set.Icc 0 1, x ^ n * factorialMomentDensity x

end MathlibPlus.Open.Research.Q0010
