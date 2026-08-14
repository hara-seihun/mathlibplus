import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The finite gamma-recurrence multiplier from the admitted claim. -/
def finiteGammaRecurrenceMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  Finset.prod (Finset.range n) (fun k => z + (k : ℂ))

/--
For every complex `z` and natural numbers `n` and `m`, under the stated
nonvanishing hypothesis, the direct gamma recurrence and its multiplier
split hold simultaneously.
-/
def gammaRecurrenceMultiplierCocycle : Prop :=
  ∀ (z : ℂ) (n m : ℕ),
    (∀ k : ℤ, 0 ≤ k → k < ((n + m : ℕ) : ℤ) → z + (k : ℂ) ≠ 0) →
      (Complex.Gamma (z + ((n + m : ℕ) : ℂ)) =
          finiteGammaRecurrenceMultiplier (n + m) z * Complex.Gamma z) ∧
        (finiteGammaRecurrenceMultiplier (n + m) z =
          finiteGammaRecurrenceMultiplier n z *
            finiteGammaRecurrenceMultiplier m (z + (n : ℂ)))

end MathlibPlus.Open.Analysis
