import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-!
Statement-fidelity registry node for admitted claim 819.  The source's exact
values are represented with Mathlib's natural prime-counting function; no
floating-point or real-cutoff convention is introduced for these integer data.
-/

/-- Claim 819: exact prime-count data at the sharp finite-range start, its next
prime, and the handoff endpoint, together with the stated primality status. -/
def exactPrimeCountDataAtSharpStart : Prop :=
  Nat.primeCounting 1526671 = 116053 ∧
    Nat.Prime 1526687 ∧
    Nat.primeCounting 1526687 = 116054 ∧
    ¬ Nat.Prime 1526671 ∧
    Nat.primeCounting 1529630 = 116255

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
