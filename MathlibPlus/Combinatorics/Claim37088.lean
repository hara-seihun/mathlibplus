import Mathlib

namespace MathlibPlus.Combinatorics

/--
Arithmetic part of Claim 37088's presentation-orbit census.  The source
connection-set and orbit carriers are kept outside this receipt; the displayed
cardinalities and Burnside product are recorded exactly.
-/
theorem claim37088_burnsideArithmetic :
    (114327628 : ℕ) ≥ 37897 ∧
      305601408 = 8064 * 37897 := by
  norm_num

end MathlibPlus.Combinatorics
