import MathlibPlus.Open.NewResearch2.R0399MatchedProfiles

namespace MathlibPlus.Open.ResearchFormalization.R0399PureLowerEdge

noncomputable section

open MathlibPlus.Open.NewResearch2.R0399MatchedProfiles

/-- The lower-edge cube vertex `p_S=j_* ∨ ⋁S`. -/
def lowerCubeCoordinate {L : Type*} [Lattice L] [OrderBot L]
    (jStar : L) (S : Finset L) : L :=
  jStar ⊔ finiteJoin S

/-- Claim 20936: the exact incidence-difference condition realizes deletion
of `j`, and the pure lower edge at `S=∅` is always matched. -/
def claim20936_pureLowerEdgeMatched : Prop :=
  ∀ {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L]
    (j : L) (T : Finset L) (jStar : L),
    canonicalTightCube j T →
      lowerCover jStar j →
        (∀ S : Finset L, S ⊆ T →
          incidence (cubeCoordinate j S) \ incidence (lowerCubeCoordinate jStar S) =
              ({j} : Set L) →
            realizes j S (lowerCubeCoordinate jStar S)) ∧
        realizes j ∅ jStar

end

end MathlibPlus.Open.ResearchFormalization.R0399PureLowerEdge
