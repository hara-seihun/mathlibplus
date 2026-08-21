-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.NumberTheory

/-- Claim 21587: exactly 52,362 primes lie in the half-open interval
`(32768, 690988]`. -/
theorem claim21587_largePrimeIntervalCount :
    Nat.primeCounting 690988 - Nat.primeCounting 32768 = 52362 := by
  native_decide

end MathlibPlus.NumberTheory
