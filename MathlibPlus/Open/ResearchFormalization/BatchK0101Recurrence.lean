import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchK0101

/-- Claim 8536: the Cholesky pivot recurrence written in normalized defect
coordinates on an approximate block. -/
def claim8536_forcedParabolicRecurrence : Prop :=
  ∀ (c : ℝ) (alpha beta q eps eta d : ℕ → ℝ) (k : ℕ),
    1 ≤ k →
    0 < c →
    alpha k = c * (2 + eps k) →
    beta k = c * (1 + eta k) →
    q (k - 1) = c * (1 + d (k - 1)) →
    q k = c * (1 + d k) →
    0 < q (k - 1) →
    q k = alpha k - beta k ^ 2 / q (k - 1) →
    d k = d (k - 1) / (1 + d (k - 1)) + eps k -
      (2 * eta k + eta k ^ 2) / (1 + d (k - 1))

end MathlibPlus.Open.ResearchFormalization.BatchK0101
