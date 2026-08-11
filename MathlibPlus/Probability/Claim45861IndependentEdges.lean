import Mathlib

namespace MathlibPlus.Probability.Claim45861

/-- Exact numerical checks for the independent-edge counterfeit in claim
45861, with the source probability and chain carriers represented by their
explicit rational values. -/
theorem independentEdgeProbabilityChecks_claim45861 :
    (2 / 3 : ℚ) ^ 2 = 4 / 9 ∧
      (2 / 3 : ℚ) ^ 4 = 16 / 81 ∧
      2 * (2 / 3 : ℚ) ^ 2 = 8 / 9 ∧
      (2 / 3 : ℚ) ^ 2 < 1 / 2 ∧
      2 * (2 / 3 : ℚ) ^ 2 ≤ 1 ∧
      0 < (2 / 3 : ℚ) ^ 4 := by
  norm_num

/-- For every chain length `k ≥ 2`, the independent-edge probability is at
most the displayed two-edge bound. -/
theorem independentEdgePowerBound_claim45861 (k : ℕ) (hk : 2 ≤ k) :
    (2 / 3 : ℚ) ^ k ≤ 4 / 9 := by
  have h := pow_le_pow_of_le_one
    (a := (2 / 3 : ℚ)) (by norm_num) (by norm_num) hk
  norm_num at h ⊢
  exact h

end MathlibPlus.Probability.Claim45861
