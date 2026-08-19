import Mathlib.NumberTheory.PrimeCounting

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 755: the exact prime count at the C-0048 split point. -/
def exactSplitPrimeCount : Prop :=
  Nat.primeCounting 247000000 = 13524076

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
