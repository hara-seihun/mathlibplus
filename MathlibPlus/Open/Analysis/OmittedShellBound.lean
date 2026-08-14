import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.OmittedShellBound

/-- The elementary Gaussian tail estimate from the admitted packet. -/
def elementaryOmittedShellBound : Prop :=
  ∀ M : ℕ, 1 ≤ M →
    (∑' m : ℕ,
        if M ≤ m then Real.exp (-Real.pi * (m : ℝ) ^ 2) else 0) ≤
      Real.exp (-Real.pi * (M : ℝ) ^ 2) +
        ∫ x in Set.Ici (M : ℝ), Real.exp (-Real.pi * x ^ 2) ∧
    Real.exp (-Real.pi * (M : ℝ) ^ 2) +
        ∫ x in Set.Ici (M : ℝ), Real.exp (-Real.pi * x ^ 2) ≤
      Real.exp (-Real.pi * (M : ℝ) ^ 2) *
        (1 + 1 / (2 * Real.pi * (M : ℝ)))

end MathlibPlus.Open.Analysis.OmittedShellBound
