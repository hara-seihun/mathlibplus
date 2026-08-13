import MathlibPlus.Open.Analysis.Claim899900
import MathlibPlus.Open.NumberTheory.PublishedDenominatorClaim1719

namespace MathlibPlus.Analysis

/-- The decimal and explicit-rational presentations of the same classical
zero-free region are equivalent. -/
theorem classicalZeroFreeRegion_iff_publishedDenominator :
    MathlibPlus.Open.Analysis.Claim899.classicalZeroFreeRegion ↔
      MathlibPlus.Open.NumberTheory.publishedDenominator_claim1719 := by
  constructor
  · intro h t σ ht hσ
    apply h t σ ht
    norm_num at hσ ⊢
    exact hσ
  · intro h t σ ht hσ
    apply h t σ ht
    norm_num at hσ ⊢
    exact hσ

end MathlibPlus.Analysis
