import MathlibPlus.Open.ResearchFormalization.R0913RootedContextChannels

namespace MathlibPlus.Open.ResearchFormalization.R0913Claim25583

noncomputable section
open Classical

/-- Claim 25583: attaching one fixed context at the distinguished port acts on
 the actual event-family feature matrix by the invertible context matrix and
therefore preserves its row span. -/
def fixedContextGraftingPreservesRowSpan25583 : Prop :=
  ∀ {R E P : Type*} [CommRing R] [CharZero R] [Fintype E] [Fintype P]
      [DecidableEq P] (context :
        MathlibPlus.Open.ResearchFormalization.R0913.RootedContext)
      (events :
        MathlibPlus.Open.ResearchFormalization.R0913.PortLabelledFamily R E P)
      (distinguished : P),
    let original :=
      MathlibPlus.Open.ResearchFormalization.R0913.familyFeatureMatrix
        events distinguished
    let attached :=
      MathlibPlus.Open.ResearchFormalization.R0913.attachedFamilyFeatureMatrix
        context events distinguished
    let U :=
      MathlibPlus.Open.ResearchFormalization.R0913.contextActionMatrix
        (MathlibPlus.Open.ResearchFormalization.R0913.aggregateJet (R := R)
          context)
    attached = U * original ∧
      U.det = 1 ∧
      Submodule.span R (Set.range (fun i : Fin 4 => attached i)) =
        Submodule.span R (Set.range (fun i : Fin 4 => original i))

end

end MathlibPlus.Open.ResearchFormalization.R0913Claim25583
