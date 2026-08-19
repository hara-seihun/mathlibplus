import Mathlib

namespace MathlibPlus.Open.NumberTheory.Totient

/-- The sharp global totient coefficient has the two stated enclosures and the
complete printed decimal prefix. -/
def sharpCoefficientNumericalEnclosure_claim668 : Prop :=
  let N₉ : ℕ := 223092870
  let coefficient : ℝ :=
    Real.log (Real.log (N₉ : ℝ)) *
      ((N₉ : ℝ) / (Nat.totient N₉ : ℝ) -
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (N₉ : ℝ)))
  let decimalPrefix : ℝ := 2.506369279696429677313820930790467588
  (2.5063692796963 : ℝ) < coefficient ∧
    coefficient < (2.5063692796966 : ℝ) ∧
    (5 / 2 : ℝ) < coefficient ∧
    coefficient < (2.50637 : ℝ) ∧
    decimalPrefix ≤ coefficient ∧
    coefficient < decimalPrefix + 1 / 10 ^ 36

end MathlibPlus.Open.NumberTheory.Totient
