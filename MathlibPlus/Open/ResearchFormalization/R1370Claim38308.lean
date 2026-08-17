import MathlibPlus.Open.ResearchFormalizationBatch01Worker01a000eb

namespace MathlibPlus.Open.ResearchFormalization.R1370Claim38308

open MathlibPlus.Open.ResearchFormalizationBatch01Worker01a000eb

noncomputable section

abbrev RegularQuaternion :=
  {Q : Subgroup (Equiv.Perm AffineThreeTwo) // IsRegularQuaternionSubgroup Q}

def generatedPairOrder
    (pair : RegularQuaternion × RegularQuaternion) : ℕ :=
  Nat.card (↥((pair.1).1 ⊔ (pair.2).1))

abbrev OrderEightPairs :=
  {pair : RegularQuaternion × RegularQuaternion //
    generatedPairOrder pair = 8}

abbrev OrderThirtyTwoPairs :=
  {pair : RegularQuaternion × RegularQuaternion //
    generatedPairOrder pair = 32}

def uniqueCommonCentralInvolution
    (Q R : RegularQuaternion) : Prop :=
  ∃ z : Equiv.Perm AffineThreeTwo,
    IsCentralInvolution Q.1 z ∧
      IsCentralInvolution R.1 z ∧
      (∀ z', IsCentralInvolution Q.1 z' → z' = z) ∧
      (∀ z', IsCentralInvolution R.1 z' → z' = z)

/-- Claim 38308: every order-eight or order-thirty-two generated pair in the
    exact regular-`Q₈` census has the same unique central involution. -/
def localCommonInvolution_claim38308 : Prop :=
  Nat.card OrderEightPairs = 14 ∧
    Nat.card OrderThirtyTwoPairs = 14 ∧
    (∀ pair : RegularQuaternion × RegularQuaternion,
      generatedPairOrder pair = 8 ∨ generatedPairOrder pair = 32 →
      uniqueCommonCentralInvolution pair.1 pair.2)

end

end MathlibPlus.Open.ResearchFormalization.R1370Claim38308
