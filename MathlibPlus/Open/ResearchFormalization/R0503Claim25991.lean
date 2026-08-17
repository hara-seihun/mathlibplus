import MathlibPlus.Algebra.Claim6218

namespace MathlibPlus.Open.ResearchFormalization.R0503Claim25991

open MathlibPlus.Algebra.Claim6218

noncomputable section

/-- Claim 25991: the exact seven-factor monomial-product span has the stable
    dimension `3N-8` for every `N≥6`. -/
def stableSevenFactorDimension_claim25991 : Prop :=
  ∀ N : ℕ, 6 ≤ N → D 7 N = 3 * N - 8

end

end MathlibPlus.Open.ResearchFormalization.R0503Claim25991
