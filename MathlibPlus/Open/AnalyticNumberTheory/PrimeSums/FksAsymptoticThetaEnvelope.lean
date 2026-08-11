import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/--
Claim 746: the Fiori--Kadiri--Swidinsky asymptotic one-sided envelope for the
signed relative Chebyshev-theta error.  `Real.rpow` expresses the displayed
real exponent `3/2` without changing it to natural-number division.
-/
def fksAsymptoticThetaEnvelope : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    let L := Real.log x
    let theta :=
      (Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).sum
        (fun p => Real.log (p : ℝ))
    (theta - x) / x ≤
      121.0961 * Real.rpow (L / 5.5666305) (3 / 2 : ℝ) *
        Real.exp (-2 * Real.sqrt (L / 5.5666305))

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
