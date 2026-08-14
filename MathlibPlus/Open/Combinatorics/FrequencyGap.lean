import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The exact pigeonhole frequency-gap assertion for the selected eight-prime modes. -/
def pigeonholeFrequencyGap : Prop :=
  let n : ℕ := Nat.choose 160 8
  (∀ (f : Fin n → ℝ),
      Function.Injective f →
      (∃ a b : ℝ,
        b - a < (28 : ℝ) / 5 ∧
        ∀ i : Fin n, f i ∈ Set.Icc a b) →
      ∃ i j : Fin n,
        i ≠ j ∧
        |f i - f j| ≤ (28 : ℝ) / (5 * ((n : ℝ) - 1))) ∧
    (28 : ℝ) / (5 * ((n : ℝ) - 1)) <
      (1 : ℝ) / (3 * (690989 : ℝ) ^ 2)

end MathlibPlus.Open.Combinatorics
