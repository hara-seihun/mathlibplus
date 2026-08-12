import Mathlib.Tactic

namespace MathlibPlus
namespace Algebra

/--
The exact cardinality arithmetic in claim 52587.  The source's finite-group
subset and gauge-action interfaces are not silently reconstructed; those
combinatorial counts remain visible as the arithmetic premises/results.
-/
theorem profileFamilySizeArithmetic_claim52587 :
    ((128 - 16 : ℕ) / 2 = 56) ∧
      (16 + 56 * 2^5 = 1808) ∧
      (1808 * 8 * 16 = 231424) := by
  norm_num

end Algebra
end MathlibPlus
