import MathlibPlus.Open.ResearchFormalization.R0913RootedContextChannels

namespace MathlibPlus.Open.Research.R0913FixedContextGrafting25579

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0913

/-- Claim 25579: grafting a fixed aggregate jet acts linearly on the
augmented `(1,d,b,q)` feature by the displayed lower-unitriangular matrix. -/
def claim25579_fixedContextGraftingIsLinear : Prop :=
  ∀ {R : Type*} [CommRing R] (j c : Jet R),
    augmentedFeature (graftedJet j c) =
      (contextActionMatrix c).mulVec (augmentedFeature j)

end

end MathlibPlus.Open.Research.R0913FixedContextGrafting25579
