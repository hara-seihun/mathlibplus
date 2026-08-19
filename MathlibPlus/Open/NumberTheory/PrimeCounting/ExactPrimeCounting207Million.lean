import Mathlib

namespace MathlibPlus.Open.NumberTheory.PrimeCounting

/-- Claim 696: the exact number of primes at most `207,000,000`. -/
def exactPrimeCounting207Million : Prop :=
  Nat.primeCounting 207000000 = 11444931

end MathlibPlus.Open.NumberTheory.PrimeCounting
