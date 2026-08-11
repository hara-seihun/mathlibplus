import Mathlib

namespace MathlibPlus.Combinatorics.Claim35019

/--
The four exact failure-histogram entries in claim 35019 sum to the displayed
failure total.  The finite permutation/subgroup census and its local
transitivity predicate are source data and are not silently redefined here.
-/
theorem localFailureHistogramTotal_claim35019 :
    (9 : ℕ) + 18 + 54 + 27 = 108 := by
  norm_num

end MathlibPlus.Combinatorics.Claim35019
