import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0054

/-- Claim 16204: the finite-representation predicate for the Erdős 261 question. -/
def Erdos261Representable (n : ℕ) : Prop :=
  0 < n ∧
    ∃ t : ℕ, 2 ≤ t ∧
      ∃ a : Fin t → ℕ,
        (∀ k, 0 < a k) ∧
          (∀ i j, i ≠ j → a i ≠ a j) ∧
            (∀ k, a k ≠ n) ∧
              (n : ℚ) / (2 : ℚ) ^ n =
                ∑ k, (a k : ℚ) / (2 : ℚ) ^ (a k)

end MathlibPlus.Open.ResearchFormalization.Q0054
