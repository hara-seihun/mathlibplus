import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeSums

/--
Claim 740: the global improved upper bound for Chebyshev's theta function.
The finite sum uses exactly the natural primes `p ≤ x` at each real cutoff.
-/
def globalImprovedThetaUpperBound : Prop :=
  ∀ x : ℝ, 1 < x →
    let theta :=
      (Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).sum
        (fun p => Real.log (p : ℝ))
    theta < x * (1 + 0.0143406585 / (Real.log x) ^ 3)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeSums
