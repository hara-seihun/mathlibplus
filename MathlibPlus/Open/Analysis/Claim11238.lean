import MathlibPlus.Open.Analysis.Claim11235_11240_11241

namespace MathlibPlus.Open.Analysis.Claim11238

open MathlibPlus.Open.Analysis

/-- Claim 11238: planting the exact nonzero polynomial `Q_m(z) = 1 + z^(4m)`
for `m ≥ 1` preserves the entire-function order of every positive finite-order
entire carrier. -/
def claim11238_finitePositiveOrderUnchangedByPlanting : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∀ F : ℂ → ℂ, hasPositiveFiniteOrder F →
      let G : ℂ → ℂ := fun z => F z * qₘ m z
      entireOrder G = entireOrder F

end MathlibPlus.Open.Analysis.Claim11238
