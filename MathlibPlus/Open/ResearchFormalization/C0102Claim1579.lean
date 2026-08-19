import MathlibPlus.Open.ResearchFormalization.C0102C0119Batch

namespace MathlibPlus.Open.ResearchFormalization.C0102Claim1579

noncomputable section

open MathlibPlus.Open.ResearchFormalization.C0102C0119

/-- Claim 1579: the cleared column family has the exact initial values and
one-step recurrence on its current carrier. -/
def claim_1579 : Prop :=
  (∀ (m : ℕ) (b : ℝ),
    clearedR 0 m b = 1 ∧ clearedR 1 m b = 2 * b) ∧
    (∀ (n m : ℕ) (b : ℝ), 2 ≤ n →
      clearedR n m b =
        (2 * b + (m : ℝ) + 2) * clearedR (n - 1) (m + 1) b +
          (-1 : ℝ) ^ n *
            (Nat.choose (m + 2 * n) n : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.C0102Claim1579
