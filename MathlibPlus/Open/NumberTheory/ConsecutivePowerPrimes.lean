import Mathlib

/-!
# Primes between consecutive powers

Statement-fidelity registry node for admitted claim 1284.  The claim supplies no
exceptional set or alternate endpoint convention, so the node retains all natural
`n ≥ 1` and strict inequalities.
-/

namespace MathlibPlus.Open.NumberTheory

/-- Claim 1284: every consecutive pair of positive 69th powers contains a prime
strictly between its endpoints. -/
def primeBetweenPowers69 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ,
    Nat.Prime p ∧ n ^ 69 < p ∧ p < (n + 1) ^ 69

end MathlibPlus.Open.NumberTheory
