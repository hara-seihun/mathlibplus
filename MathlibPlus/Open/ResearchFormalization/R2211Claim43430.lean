import MathlibPlus.Open.Research.R2211ExactImageRepair

namespace MathlibPlus.Open.ResearchFormalization.R2211Claim43430

open MathlibPlus.Open.Research.R2211
open MathlibPlus.Open.Research.R2211ExactImageRepair

noncomputable section

def explicitFiniteModel_claim43430 : Prop :=
  ∃ x y g : Equiv.Perm H,
    (∀ h : H, x h = xMap h) ∧
      (∀ h : H, y h = yMap h) ∧
        (∀ h : H, g h = gMap h) ∧
          let X := generatedX x y
          Set.ncard (X : Set (Equiv.Perm H)) = 3 ^ 7 ∧
            Set.ncard (X : Set (Equiv.Perm H)) = 2187

end

end MathlibPlus.Open.ResearchFormalization.R2211Claim43430
