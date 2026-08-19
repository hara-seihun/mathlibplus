import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-- Claim 1721: the published BTY zero-free region with its closed
`σ` boundary and its stated lower height. -/
def btyPublishedZetaZeroFree_claim1721 : Prop :=
  ∀ (t σ : ℝ),
    3 ≤ t →
    1 - 1 / ((4.896 : ℝ) * Real.log t) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
