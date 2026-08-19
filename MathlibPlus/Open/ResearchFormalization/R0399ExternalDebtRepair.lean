import MathlibPlus.Open.NewResearch2.R0399MatchedProfiles
import MathlibPlus.Open.Research.FormalizationBatch01a00431.Collision

open Classical
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0399ExternalDebtRepair

noncomputable section

open MathlibPlus.Open.NewResearch2.R0399MatchedProfiles

/-- The finite join-irreducible coordinate carrier of a finite lattice. -/
def joinIrreducibles {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] : Finset L :=
  Finset.univ.filter (fun u => joinIrreducible u)

/-- The join-irreducible incidence carrier as a finite set. -/
def incidenceFinset {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (x : L) : Finset L :=
  (joinIrreducibles (L := L)).filter (fun u => u ≤ x)

/-- The ordinary family complementary to lattice incidence. -/
def complementaryMember {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (x : L) : Finset L :=
  joinIrreducibles (L := L) \ incidenceFinset x

/-- The complementary ordinary distinct family represented by the lattice. -/
def complementaryFamily {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] : Finset (Finset L) :=
  Finset.univ.image (fun x : L => complementaryMember x)

/-- The complete collision shadow, retaining only the endpoint without `j`. -/
def actualCollisionShadow {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (j : L) : Finset (Finset L) :=
  MathlibPlus.Open.Research.FormalizationBatch.collisionShadow20524
    (joinIrreducibles (L := L)) (complementaryFamily (L := L)) j

/-- The canonical collision block is the part of the actual shadow indexed by
matched canonical cube vertices. -/
def canonicalCollisionBlock {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (j : L) (T : Finset L) : Finset (Finset L) :=
  (actualCollisionShadow j).filter (fun A =>
    ∃ S : Finset L,
      S ∈ matchedToggleProfile_claim20930 j T ∧
        A = complementaryMember (cubeCoordinate j S))

/-- The external collision profile is the complete shadow outside the
canonical transported block. -/
def externalCollisionProfile {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (j : L) (T : Finset L) : Finset (Finset L) :=
  actualCollisionShadow j \ canonicalCollisionBlock j T

/-- The tight-coordinate deficit of a finite collision block. -/
def tightDebt {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L]
    (B : Finset (Finset L)) (t : L) : ℤ :=
  (B.card : ℤ) - 2 * ((B.filter (fun A => t ∈ A)).card : ℤ)

/-- Exactness of the three tight traces on the canonical cube. -/
def exactTightTraces {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (j : L) (T : Finset L) : Prop :=
  ∀ S : Finset L, S ⊆ T →
    ∀ t : L, t ∈ T →
      t ∈ incidence (cubeCoordinate j S) ↔ t ∈ S

/-- The lower endpoint attempted by transporting the lower cover through a
cube vertex. -/
def lowerCubeCoordinate {L : Type*} [Lattice L] [OrderBot L]
    (jStar : L) (S : Finset L) : L :=
  cubeCoordinate jStar S

/-- Purity of the transported lower-cover edge at a cube vertex. -/
def pureLowerEdge {L : Type*} [Lattice L] [OrderBot L]
    (jStar j : L) (S : Finset L) : Prop :=
  incidence (cubeCoordinate j S) \ incidence (lowerCubeCoordinate jStar S) = {j}

/-- Claim 20935: with the exact tight traces, any positive debt in the
complete collision shadow is at least that debt in the external profile. -/
def claim20935 : Prop :=
  ∀ {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L]
    (j : L) (T : Finset L),
    canonicalTightCube j T →
      exactTightTraces j T →
        ∀ t ∈ T,
          0 < tightDebt (actualCollisionShadow j) t →
            tightDebt (externalCollisionProfile j T) t ≥
              tightDebt (actualCollisionShadow j) t

/-- Claim 20941: the 105-member fixture has pure matched transport at all
cube vertices, yet positive full tight debt is carried by seventeen external
collisions. -/
def claim20941 : Prop :=
  ∃ (L : Type*) (fintype : Fintype L) (decEq : DecidableEq L)
      (lattice : Lattice L) (bounded : BoundedOrder L),
    letI : Fintype L := fintype
    letI : DecidableEq L := decEq
    letI : Lattice L := lattice
    letI : BoundedOrder L := bounded
    ∃ (j jStar : L) (T : Finset L),
      canonicalTightCube j T ∧
        lowerCover jStar j ∧
        exactTightTraces j T ∧
        (complementaryFamily (L := L)).card = 105 ∧
        (∀ S : Finset L, S ⊆ T →
          pureLowerEdge jStar j S ∧
            S ∈ matchedToggleProfile_claim20930 j T) ∧
        (canonicalCollisionBlock j T).card = 8 ∧
        (externalCollisionProfile j T).card = 17 ∧
        (∀ t ∈ T,
          tightDebt (canonicalCollisionBlock j T) t = 0 ∧
            tightDebt (externalCollisionProfile j T) t = 1 ∧
            tightDebt (actualCollisionShadow j) t = 1) ∧
        canonicalCollisionBlock j T ∪ externalCollisionProfile j T =
          actualCollisionShadow j

end

end MathlibPlus.Open.ResearchFormalization.R0399ExternalDebtRepair
