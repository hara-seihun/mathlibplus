import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 751: the improved global eight-term prime-counting bound.  On real
arguments, the source's `π` is represented by the number of primes at most the
natural floor, and the displayed decimal coefficients are exact real literals. -/
def improvedGlobalEightTermBound : Prop :=
  ∀ x : ℝ, 1 < x →
    let L := Real.log x
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      x / L + x / L ^ 2 + 2 * x / L ^ 3 +
        6.024334 * x / L ^ 4 + 24 * x / L ^ 5 +
        120 * x / L ^ 6 + 720 * x / L ^ 7 +
        6097.2 * x / L ^ 8

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
