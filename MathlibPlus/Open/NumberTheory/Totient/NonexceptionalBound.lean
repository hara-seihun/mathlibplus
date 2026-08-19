import Mathlib

namespace MathlibPlus.Open.NumberTheory.Totient

/-- Every integer at least three other than the ninth primorial satisfies the
strict Rosser--Schoenfeld bound and its equivalent normalized-error form. -/
def nonexceptionalBound_claim666 : Prop :=
  let N₉ : ℕ := 223092870
  let totientError : ℕ → ℝ := fun n ↦
    Real.log (Real.log (n : ℝ)) *
      ((n : ℝ) / (Nat.totient n : ℝ) -
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)))
  ∀ n : ℕ, 3 ≤ n → n ≠ N₉ →
    (n : ℝ) / (Nat.totient n : ℝ) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
          (5 / 2 : ℝ) / Real.log (Real.log (n : ℝ)) ∧
      totientError n < (5 / 2 : ℝ)

end MathlibPlus.Open.NumberTheory.Totient
