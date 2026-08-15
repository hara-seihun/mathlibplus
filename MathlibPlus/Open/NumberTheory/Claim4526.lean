import Mathlib

namespace MathlibPlus.Open.NumberTheory.Claim4526

/-- The numerical endpoint of the degree-56 transfer. -/
def degree56TransferEndpoint_claim4526 : Prop :=
  (∀ n m : ℕ, n ≤ 27 → m ≤ n → 2 * m ≤ 54 ∧ 54 < 56) ∧
    (∃ n m : ℕ,
      n = 28 ∧ m = 28 ∧ m ≤ n ∧ 2 * m = 56 ∧ 56 ≤ 2 * m) ∧
    ¬(∀ m : ℕ, m ≤ 28 → 2 * m < 56)

end MathlibPlus.Open.NumberTheory.Claim4526
