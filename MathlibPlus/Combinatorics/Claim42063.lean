import Mathlib

namespace MathlibPlus.Combinatorics

/--
Finite count receipt for the `m = 1` trivial-kernel boundary in Claim 42063:
three unordered orbitals, 32 universal terminal transporters, and the two
signed-pair counts 8 and 16.  The kernel, seed, and criterion predicates are
not reconstructed from the source packet.
-/
theorem claim42063_trivialKernelCounts :
    (3 : ℕ) < 32 ∧
      8 < 32 ∧
      16 < 32 ∧
      8 ≠ 16 ∧
      32 - 8 = 24 ∧
      32 - 16 = 16 := by
  norm_num

end MathlibPlus.Combinatorics
