import MathlibPlus.Open.ResearchFormalization.EulerPascalSignsClaim18160

namespace MathlibPlus.Open.ResearchFormalization.BatchR0131Claim18156

noncomputable section

open MathlibPlus.Open.ResearchFormalization.BatchR0131

/-- The Euler--Pascal factor and terminal convolution use the displayed finite
subset carrier, positive-index convention, and exact sparse moment indices. -/
def claim18156_eulerPascalCoefficientArray : Prop :=
  (∀ (m l : ℕ),
    eulerPascalFactor m l =
      if 0 < m ∧ 0 < l then
        (1 / (((2 * m : ℕ) : ℝ))) *
          eulerPascalElementarySymmetric m (l - 1)
      else 0) ∧
  (∀ (m k : ℕ),
    eulerPascalElementarySymmetric m k =
      ∑ s ∈ (Finset.range (m - 1)).powerset,
        if s.card = k then
          ∏ r ∈ s, (1 / (((2 * (r + 1) : ℕ) : ℝ)))
        else 0) ∧
  (∀ (μ : ℕ → ℝ) (l j : ℕ),
    eulerPascalTerminalConvolution μ l j =
      if 0 < l ∧ l ≤ 2 * j then 2 * μ (2 * j - l) else 0)

end

end MathlibPlus.Open.ResearchFormalization.BatchR0131Claim18156
