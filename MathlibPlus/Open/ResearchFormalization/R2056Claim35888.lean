import MathlibPlus.Open.ResearchFormalization.R2056.C35884
import MathlibPlus.Open.ResearchFormalization.R2056.C35886

namespace MathlibPlus.Open.ResearchFormalization.R2056Claim35888

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2056C35884

abbrev GridIndex := Fin 3 × Fin 3

/-- The canonical ordering used to enumerate unordered pairs of the nine
actual grid points. -/
def pointPairLess (a b : GridIndex) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

noncomputable def allSquaredDistancePairs : Finset (GridIndex × GridIndex) :=
  letI : DecidablePred (fun pair : GridIndex × GridIndex =>
      pointPairLess pair.1 pair.2) :=
    fun _ => Classical.propDecidable _
  Finset.univ.filter (fun pair : GridIndex × GridIndex =>
    pointPairLess pair.1 pair.2)

noncomputable def unitDistancePairs : Finset (GridIndex × GridIndex) :=
  letI : DecidablePred (fun pair : GridIndex × GridIndex =>
      unitPair pair.1.1 pair.1.2 pair.2.1 pair.2.2) :=
    fun _ => Classical.propDecidable _
  allSquaredDistancePairs.filter (fun pair : GridIndex × GridIndex =>
    unitPair pair.1.1 pair.1.2 pair.2.1 pair.2.2)

/-- Claim 35888: the exact finite enumeration ranges over all 36 unordered
point pairs, finds exactly the twelve grid edges at unit length, and retains
the four rhombic orientations and six projective direction separations. -/
def claim35888_exactFiniteVerifier : Prop :=
  MathlibPlus.Open.ResearchFormalization.R2056C35884.claim35884_embeddingAndFaceToFace ∧
    MathlibPlus.Open.ResearchFormalization.R2056C35886.claim35886_directionCrossingK22 ∧
      allSquaredDistancePairs.card = 36 ∧
        unitDistancePairs.card = 12 ∧
          (∀ pair ∈ allSquaredDistancePairs,
            unitPair pair.1.1 pair.1.2 pair.2.1 pair.2.2 ↔
              gridAdjacent pair.1.1 pair.1.2 pair.2.1 pair.2.2) ∧
            (∀ i j : Fin 2, cellIsRhombus i j)

end

end MathlibPlus.Open.ResearchFormalization.R2056Claim35888
