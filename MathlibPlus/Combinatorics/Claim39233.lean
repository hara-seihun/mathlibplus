import Mathlib

namespace MathlibPlus.Combinatorics.Claim39233

/-- RECEIPT for the two displayed arithmetic counts in the support-two census;
the packet-specific chart, support, and fibre-action carriers are not
reconstructed here. -/
theorem support_two_count_claim39233 :
    12 * Nat.choose 26 2 = 3900 ∧
      (3900 : ℕ) * 48 = 187200 := by
  norm_num [Nat.choose]

end MathlibPlus.Combinatorics.Claim39233
