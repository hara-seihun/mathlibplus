import MathlibPlus.Algebra.Claim6218

namespace MathlibPlus.Open.ResearchFormalization.R0504Claim26011

open MathlibPlus.Algebra.Claim6218

noncomputable section

/-- Claim 26011: the exact eight-factor monomial-product span has the stable
    dimension `3N+floor(N/2)-11` for every `N≥8`. -/
def stableEightFactorDimension_claim26011 : Prop :=
  ∀ N : ℕ, 8 ≤ N → D 8 N = 3 * N + N / 2 - 11

end

end MathlibPlus.Open.ResearchFormalization.R0504Claim26011
