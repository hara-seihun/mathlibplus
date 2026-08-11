import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 929: Mathlib's `Nat.primeCounting` is the formal reading of the
source's integer prime-counting function `π` at the stated finite split. -/
def exactPrimeCountAtFiniteSplit_claim929 : Prop :=
  Nat.primeCounting 205000000 = 11340473

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
