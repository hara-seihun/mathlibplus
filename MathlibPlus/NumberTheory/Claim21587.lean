-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib.NumberTheory.Chebyshev

namespace MathlibPlus.NumberTheory

/-- Claim 21587: exactly 52,362 primes lie in the half-open interval
`(32768, 690988]`. -/
theorem claim21587_largePrimeIntervalCount :
    Nat.primeCounting 690988 - Nat.primeCounting 32768 = 52362 := by
  native_decide

end MathlibPlus.NumberTheory
