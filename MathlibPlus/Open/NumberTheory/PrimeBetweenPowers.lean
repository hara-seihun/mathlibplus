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

/-!
Statement-fidelity registry node for admitted claim 939.  The source gives the
constant as `(34/1327) log⁴(1327)`, with a decimal display of its value; the
formal statement retains the exact logarithmic expression.
-/

/-- Claim 939: every real `x ≥ 2` has a prime in the stated order-four interval. -/
def improvedOrderFourPrimeInterval : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ,
    Nat.Prime p ∧ x < (p : ℝ) ∧
      (p : ℝ) ≤ x *
        (1 + ((34 : ℝ) / 1327) * (Real.log 1327) ^ 4 / (Real.log x) ^ 4)

end MathlibPlus.Open.NumberTheory
