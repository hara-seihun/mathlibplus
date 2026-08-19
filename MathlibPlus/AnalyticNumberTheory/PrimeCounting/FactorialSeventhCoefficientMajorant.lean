import MathlibPlus.AxlerMajorant

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-! Claim 691: expose the exact C-0044 factorial-seventh-coefficient
majorant under its claim-specific declaration name. -/

def factorialSeventhCoefficientMajorant (x : ℝ) : ℝ :=
  MathlibPlus.AxlerMajorant.factorial720Bound x

end

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
