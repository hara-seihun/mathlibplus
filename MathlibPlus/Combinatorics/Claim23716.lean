import Mathlib

namespace MathlibPlus.Combinatorics.Claim23716

/-- Exact numerical receipts in the degree-six representative census.  The
mixed-matrix, GRR, and canonical-owner carriers are intentionally not
reconstructed from the source packet. -/
theorem degreeSixRepresentativeCensusArithmetic_claim23716 :
    (7435992 : ℕ) = 6743243 + 692749 ∧
      (7435992 : ℕ) - 6743243 = 692749 ∧
      (8185 : ℕ) + 3 = 8188 ∧
      (8188 : ℕ) - 8185 = 3 := by
  norm_num

end MathlibPlus.Combinatorics.Claim23716
