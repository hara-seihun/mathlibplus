import Mathlib.NumberTheory.PrimeCounting

/-!
# Exact prime count at 205 million

This registry node is the exact finite numerical assertion in admitted claim 634.
-/

namespace MathlibPlus.Open.NumberTheory.PrimeCounting

/-- Exactly `11,340,473` primes are at most `205,000,000`. -/
def exactPrimeCounting205Million : Prop :=
  Nat.primeCounting 205000000 = 11340473

end MathlibPlus.Open.NumberTheory.PrimeCounting
