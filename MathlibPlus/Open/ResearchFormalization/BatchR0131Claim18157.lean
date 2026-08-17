import MathlibPlus.Open.ResearchFormalization.EulerPascalSignsClaim18160

namespace MathlibPlus.Open.ResearchFormalization.BatchR0131Claim18157

noncomputable section

/-- The Taylor array is the exact Euler--Pascal factor followed with the sparse
terminal convolution.  The index `l + 1` makes the displayed finite sum the
same as `1 ≤ ell ≤ 2j`, including the zero branches of the sparse factor. -/
def claim18157_exactFactorizationEC : Prop :=
  ∀ (μ : ℕ → ℝ) (m j : ℕ),
    MathlibPlus.Open.ResearchFormalization.BatchR0131.eulerPascalTaylorArray μ m j =
      2 * ∑ l ∈ Finset.range (2 * j),
        MathlibPlus.Open.ResearchFormalization.BatchR0131.eulerPascalFactor m (l + 1) *
          μ (2 * j - (l + 1))

end

end MathlibPlus.Open.ResearchFormalization.BatchR0131Claim18157
