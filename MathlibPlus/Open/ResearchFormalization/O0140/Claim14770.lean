import MathlibPlus.Open.ResearchFormalization.FreeOrbitGeneratorIdentitiesClaim14780

namespace MathlibPlus.Open.ResearchFormalization.O0140.Claim14770

open MathlibPlus.Open.ResearchFormalization.FreeOrbitGeneratorIdentitiesClaim14780

noncomputable section

/-- Every mixed finite-prime signed-permutation orbit is free under the exact
normalized arithmetic point and prime hypotheses. -/
def everyMixedFinitePrimeOrbitIsFree_claim14770 : Prop :=
  ∀ (p : ℕ) (α : ℂ),
    mixedFinitePrimeHypothesis p α → mixedPrimeOrbitFree p α

end

end MathlibPlus.Open.ResearchFormalization.O0140.Claim14770
