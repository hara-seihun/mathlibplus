import MathlibPlus.Open.ResearchFormalization.R0322Claim19813

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19815

open scoped BigOperators Classical

noncomputable section

/-- The admitted all-order rank formula for the supplied specialization model. -/
def allOrderRankFormula_claim19815 : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    MathlibPlus.Open.ResearchFormalization.R0322Claim19813.rankGamma k =
      k + ∑ i ∈ Finset.Icc 2 k, Nat.choose (i / 2) 2

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19815
