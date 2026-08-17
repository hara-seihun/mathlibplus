import MathlibPlus.Open.ResearchFormalization.R0913RootedContextChannels

namespace MathlibPlus.Open.ResearchFormalization.R0913Claim25584

open MathlibPlus.Open.ResearchFormalization.R0913

noncomputable section

/-- Claim 25584: attaching one fixed rooted context at the distinguished port
left-multiplies the exact local feature matrix by its context-action matrix,
so every right-kernel vector and the column rank are preserved. -/
def claim25584 : Prop :=
  ∀ {R E P : Type*} [CommRing R] [CharZero R] [Fintype E] [Fintype P]
    [DecidableEq P] (context : RootedContext)
    (events : PortLabelledFamily R E P) (distinguished : P),
    let original := familyFeatureMatrix events distinguished
    let attached := attachedFamilyFeatureMatrix context events distinguished
    let U := contextActionMatrix (aggregateJet context)
    attached = U * original ∧
      (∀ x : E → R,
        localKernelCondition attached x ↔ localKernelCondition original x) ∧
      attached.rank = original.rank

end

end MathlibPlus.Open.ResearchFormalization.R0913Claim25584
