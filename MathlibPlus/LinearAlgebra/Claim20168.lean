import Mathlib.Tactic

namespace MathlibPlus
namespace LinearAlgebra

/-- Exact binomial coefficient evaluation in claim 20168.  The additional
nonzero-mode and `ℚ^8` distinctness assertions are source-specific and are not
silently replaced by this arithmetic certificate. -/
theorem exactEightSubsetCount_claim20168 :
    Nat.choose 160 8 = 8917061687820 := by
  norm_num [Nat.choose]

end LinearAlgebra
end MathlibPlus
