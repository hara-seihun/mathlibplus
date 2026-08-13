import Mathlib

namespace MathlibPlus.NumberTheory.Claim9615

/-- The left Tidelaw strand-roster function. -/
def L (d : ℕ) : ℕ := Nat.gcd 4 d * Nat.gcd 6 d

/-- The right Tidelaw strand-roster function. -/
def R (d : ℕ) : ℕ := Nat.gcd 2 d * Nat.gcd 12 d

end MathlibPlus.NumberTheory.Claim9615
