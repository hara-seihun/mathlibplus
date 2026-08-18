import MathlibPlus.Open.ResearchFormalization.R1184StructuralFactsClaim41742

namespace MathlibPlus.Open.ResearchFormalization.R1184Claim41741

open MathlibPlus.Open
open MathlibPlus.Open.ResearchFormalization60980
open MathlibPlus.Open.ResearchFormalization.R1184StructuralFactsClaim41742

/-- Conjugation by the displayed order-eight generator is inversion on the
    displayed odd cyclic factor. -/
def orderEightInvertsRotation (m : ℕ) : Prop :=
  ∀ u : ZMod m,
    eMul m 8
        (eMul m 8 (eInv m 8 (eB m)) (u, 0))
        (eB m) = (-u, 0)

/-- The displayed generators generate the explicit carrier. -/
def displayedGeneratorsGenerate (m : ℕ) : Prop :=
  eGenerated m ({eA m, eB m} : Set (eCarrier m 8)) = Set.univ

/-- Claim 41741: the explicit `ZMod m × ZMod 8` carrier has the displayed
    presentation, with the order-eight generator acting by inversion. -/
def claim41741 : Prop :=
  ∀ (m : ℕ),
    Odd m →
      eGroupAxioms m ∧
        ePresentationRelations m ∧
          displayedGeneratorsGenerate m ∧
            orderEightInvertsRotation m

end MathlibPlus.Open.ResearchFormalization.R1184Claim41741
