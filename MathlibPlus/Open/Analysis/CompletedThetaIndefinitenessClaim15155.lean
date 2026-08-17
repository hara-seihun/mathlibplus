import MathlibPlus.Open.Analysis.CompletedThetaIndefinitenessClaim15153

namespace MathlibPlus.Open.Analysis.CompletedThetaIndefinitenessClaim15155

open MathlibPlus.Open.Analysis.CompletedThetaIndefinitenessClaim15153
open scoped ComplexOrder

noncomputable section

/-- Claim 15155.  The total channel is the literal `q = 1` cumulative
channel, and a nontrivial channel is indexed by an integer `q > 1`.  The
feature carrier and the central matrix are the reviewed literal carriers of
Claim 15153, so no disjointness or independence assumption is added. -/
def arbitraryRedundantFiniteLinearFeaturesAreCentrallyIndefinite_claim15155 : Prop :=
  ∀ (m : ℕ) (features : Fin m → ℕ → ℂ) (q : ℕ),
    1 < q →
    shellFeatureSpanContains features 1 →
    shellFeatureSpanContains features q →
    ¬ (shellFeatureFirstLaguerreMatrix features 0).PosSemidef

end

end MathlibPlus.Open.Analysis.CompletedThetaIndefinitenessClaim15155
