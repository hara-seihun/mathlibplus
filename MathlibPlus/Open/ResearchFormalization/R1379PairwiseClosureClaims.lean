import MathlibPlus.Open.ResearchFormalization.R1379MorrisCounterexample

namespace MathlibPlus.Open.ResearchFormalization.R1379PairwiseClosureClaims

open MathlibPlus.Open.ResearchFormalization.R1379MorrisCounterexample

/-- The ordered-pair realization carrier for a linear vector-valued code. -/
def pairwiseClosure_claim38400
    {𝕜 D H : Type*} [Semiring 𝕜] [AddCommMonoid D] [Module 𝕜 D]
    (C : Submodule 𝕜 (H → D)) : Set (H → D) :=
  {s | ∀ x y : H, ∃ k : C, (k.1 x, k.1 y) = (s x, s y)}

private abbrev TwoCoordinates := {S : Finset H // S.card = 2}

private def restrictionToPair (S : TwoCoordinates) (s : Profile) : S.1 → D :=
  fun x => s x.1

private def pairProjectionImage (S : TwoCoordinates) : Set (S.1 → D) :=
  restrictionToPair S '' (code : Set Profile)

private def reconstructedPairwiseClosure : Set Profile :=
  {s | ∀ S : TwoCoordinates,
    restrictionToPair S s ∈ pairProjectionImage S}

private def pairwiseClosureSpace : Submodule F Profile :=
  Submodule.span F (pairwiseClosure_claim38400 code)

private def differenceImageSet : Set Profile :=
  {d | ∃ s : {s : Profile // s ∈ pairwiseClosure_claim38400 code},
    d = baseTranslate (0, 1) s.1 - s.1}

private def differenceImageSpace : Submodule F Profile :=
  Submodule.span F differenceImageSet

/-- The displayed fifth row is normalized for the order-three translation. -/
def normalizedNormZeroProfile_claim38402 : Prop :=
  row5 ∈ code ∧
    row5 (0, 0) = (0, 0) ∧
    row5 + baseTranslate (0, 1) row5 +
        baseTranslate (0, 1) (baseTranslate (0, 1) row5) = 0

/-- The exact row-reduction dimensions, together with reconstruction from all
36 unordered two-coordinate projections. -/
def dimensionsOfPairwiseClosure_claim38403 : Prop :=
  Module.finrank F code = 7 ∧
    pairwiseClosure_claim38400 code = (pairwiseClosureSpace : Set Profile) ∧
    Module.finrank F pairwiseClosureSpace = 12 ∧
    differenceImageSet = (differenceImageSpace : Set Profile) ∧
    Module.finrank F differenceImageSpace = 6 ∧
    pairwiseClosure_claim38400 code = reconstructedPairwiseClosure ∧
    Fintype.card TwoCoordinates = 36

/-- The coordinate-sum functional at (1,0) separates the normalized profile
from the translation-difference image. -/
def separatingFunctionalProvesNonintegrability_claim38404 : Prop :=
  (∀ d : {d : Profile // d ∈ differenceImageSet},
    (d.1 (1, 0)).1 + (d.1 (1, 0)).2 = 0) ∧
    ((row5 (1, 0)).1 + (row5 (1, 0)).2 = 1) ∧
    row5 ∉ differenceImageSet ∧
    ¬ ∃ s : {s : Profile // s ∈ pairwiseClosure_claim38400 code},
      baseTranslate (0, 1) s.1 - s.1 = row5

end MathlibPlus.Open.ResearchFormalization.R1379PairwiseClosureClaims
