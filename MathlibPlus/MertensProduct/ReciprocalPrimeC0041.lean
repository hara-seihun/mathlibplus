import Mathlib

open scoped BigOperators

namespace MathlibPlus.MertensProduct

noncomputable section

/-- The reciprocal-prime error in the `C-0041` notation, with the real cutoff
represented by the primes at most `⌊x⌋₊`. -/
def reciprocalPrimeError (B x : ℝ) : ℝ :=
  (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / (p : ℝ)) -
    Real.log (Real.log x) - B

/-- The two-term inverse-logarithmic lower-bound coefficient from `C-0041`. -/
def reciprocalPrimeErrorEnvelope (L : ℝ) : ℝ :=
  1 / (20 * L) + 3 / (16 * L ^ 2)

/-- The splice coefficient obtained by evaluating the envelope at `log 10^8`. -/
def reciprocalPrimeSpliceCoefficient : ℝ :=
  reciprocalPrimeErrorEnvelope (Real.log ((10 : ℝ) ^ 8))

end

end MathlibPlus.MertensProduct
