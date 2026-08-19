import Mathlib

namespace MathlibPlus.Open.NumberTheory.Totient

/-- The exact rounded coefficient gives the strict all-integer totient bound. -/
def strictRoundedBound_claim669 : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (n : ℝ) / (Nat.totient n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        (2.50636928 : ℝ) / Real.log (Real.log (n : ℝ))

end MathlibPlus.Open.NumberTheory.Totient
