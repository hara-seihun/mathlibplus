import Mathlib

/-!
# Axler infinite-tail prime-counting estimate

Statement-fidelity registry node for admitted claim 822. The source's
`π(x)` is represented by `Nat.primeCounting (Nat.floor x)`, matching the
real-cutoff convention used by the other prime-counting registry nodes. The
source also writes an equivalent `A(x) < 1.083` formulation, but `A` is not
defined in the admitted claim record; no unidentified function is silently
introduced here.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 822: Axler's strict infinite-tail estimate with exact coefficient
`1.083 = 1083 / 1000`. -/
def axlerInfiniteTailEstimate : Prop :=
  ∀ x : ℝ, (1529630 : ℝ) ≤ x →
    (Nat.primeCounting (Nat.floor x) : ℝ) <
      x / (Real.log x - (1083 : ℝ) / 1000)

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
