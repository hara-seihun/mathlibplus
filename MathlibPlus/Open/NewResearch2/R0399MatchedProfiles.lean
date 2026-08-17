import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0399MatchedProfiles

open scoped BigOperators

noncomputable section

/-- Intrinsic join-irreducibility in the finite lattice. -/
def joinIrreducible {L : Type*} [Lattice L] [OrderBot L]
    (u : L) : Prop :=
  u ≠ ⊥ ∧ ∀ a b : L, u = a ⊔ b → u = a ∨ u = b

/-- The join-irreducible incidence coordinates of a lattice element. -/
def incidence {L : Type*} [Lattice L] [OrderBot L]
    (x : L) : Set L :=
  {u : L | joinIrreducible u ∧ u ≤ x}

/-- The finite join of a cube subset. -/
def finiteJoin {L : Type*} [Lattice L] [OrderBot L]
    (S : Finset L) : L :=
  S.sup id

/-- The canonical cube coordinate `q_S = j ∨ ⋁ₜ∈S t`. -/
def cubeCoordinate {L : Type*} [Lattice L] [OrderBot L]
    (j : L) (S : Finset L) : L :=
  j ⊔ finiteJoin S

/-- The exact finite-lattice hypotheses for an outside join-irreducible and
three tight join-irreducible coordinates. -/
def canonicalTightCube {L : Type*} [Fintype L] [DecidableEq L]
    [Lattice L] [BoundedOrder L] (j : L) (T : Finset L) : Prop :=
  j ∉ T ∧ T.card = 3 ∧ joinIrreducible j ∧
    ∀ t ∈ T, joinIrreducible t

/-- `r` realizes a cube subset when its join-irreducible incidence is the
incidence of `q_S` with the outside label `j` deleted. -/
def realizes {L : Type*} [Lattice L] [OrderBot L]
    (j : L) (S : Finset L) (r : L) : Prop :=
  incidence (cubeCoordinate j S) \ {j} = incidence r

/-- Claim 20930: the matched-toggle profile is the exact set of subsets of
`T` whose deleted incidence is realized by a lattice element. -/
def matchedToggleProfile_claim20930
    {L : Type*} [Fintype L] [DecidableEq L] [Lattice L] [BoundedOrder L]
    (j : L) (T : Finset L) : Set (Finset L) :=
  {S : Finset L |
    S ⊆ T ∧ ∃ r : L, realizes j S r}

/-- Claim 20930: the canonical orphan profile is the complement of the
matched-toggle profile inside the powerset of `T`. -/
def canonicalOrphanProfile_claim20930
    {L : Type*} [Fintype L] [DecidableEq L] [Lattice L] [BoundedOrder L]
    (j : L) (T : Finset L) : Set (Finset L) :=
  {S : Finset L |
    S ⊆ T ∧ S ∉ matchedToggleProfile_claim20930 j T}

/-- The lower-cover relation used by the empty-cube vertex. -/
def lowerCover {L : Type*} [Lattice L]
    (jStar j : L) : Prop :=
  jStar < j ∧ ¬ ∃ x : L, jStar < x ∧ x < j

/-- Claim 20931: the matched profile is a downset containing the empty
subset; every realization transports downward by meeting with the smaller
cube coordinate, and the lower cover `j_*` realizes deletion at `S=∅`. -/
def claim20931 : Prop :=
  ∀ {L : Type*} [Fintype L] [DecidableEq L] [Lattice L] [BoundedOrder L]
    (j : L) (T : Finset L) (jStar : L),
    canonicalTightCube j T →
      lowerCover jStar j →
        (∀ S : Finset L,
          S ∈ matchedToggleProfile_claim20930 j T →
            ∀ S' : Finset L, S' ⊆ S →
              S' ∈ matchedToggleProfile_claim20930 j T) ∧
        (∅ : Finset L) ∈ matchedToggleProfile_claim20930 j T ∧
        (∀ (S : Finset L) (r : L),
          S ∈ matchedToggleProfile_claim20930 j T →
            realizes j S r →
              ∀ S' : Finset L, S' ⊆ S →
                realizes j S' (r ⊓ cubeCoordinate j S')) ∧
        realizes j ∅ jStar

end

end MathlibPlus.Open.NewResearch2.R0399MatchedProfiles
