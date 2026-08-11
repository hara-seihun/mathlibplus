import Mathlib

/-!
# Prime between consecutive 86th powers

Statement-fidelity registry node for admitted claim 1354.  The source gives no
finite exceptional set and says "between" the two endpoints, so the node uses
all natural `n ≥ 1` and strict inequalities.
-/

namespace MathlibPlus.Open.NumberTheory

/-- Claim 1354: every consecutive pair of 86th powers beginning at `n ≥ 1`
contains a prime strictly between its endpoints. -/
def primeBetweenPowers86 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ,
    Nat.Prime p ∧ n ^ 86 < p ∧ p < (n + 1) ^ 86

end MathlibPlus.Open.NumberTheory
