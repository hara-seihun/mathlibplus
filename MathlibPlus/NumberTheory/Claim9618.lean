import Mathlib

namespace MathlibPlus.NumberTheory.Claim9618

/-- The all-depth roster attached to the first finite Euler value. -/
def L (d : ℕ) : ℕ := Nat.gcd 4 d * Nat.gcd 6 d

/-- The all-depth roster attached to the second finite Euler value. -/
def R (d : ℕ) : ℕ := Nat.gcd 2 d * Nat.gcd 12 d

/-- No function of an all-depth roster recovers both finite Euler values in Record 13. -/
def no_roster_only_euler_recovery : Prop :=
  ¬ ∃ recover : (ℕ → ℕ) → ℚ,
      recover L = (35 : ℚ) / 24 ∧ recover R = (13 : ℚ) / 8

end MathlibPlus.NumberTheory.Claim9618
