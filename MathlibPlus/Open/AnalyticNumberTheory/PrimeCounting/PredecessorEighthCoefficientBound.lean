import MathlibPlus.AxlerMajorant

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

/-! Claim 690: the predecessor eight-term majorant is retained as the input
bound, with the real prime-counting convention made explicit. -/

def predecessorEighthCoefficientBound : Prop :=
  ∀ x : ℝ, 1 < x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) <
      MathlibPlus.AxlerMajorant.predecessorBound x

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
