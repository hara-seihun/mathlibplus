import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.Claim20801Repair

noncomputable section

/-- Join-irreducible coordinates in the lattice order. -/
def joinIrreducibleCoordinate {α : Type*}
    [SemilatticeSup α] [OrderBot α] (j : α) : Prop :=
  j ≠ ⊥ ∧
    ∀ a b : α, j = a ⊔ b → j = a ∨ j = b

/-- The join-irreducible coordinates below a lattice element. -/
noncomputable def joinIrreduciblesBelow {α : Type*}
    [SemilatticeSup α] [OrderBot α] [Fintype α] (x : α) : Finset α :=
  let _ : DecidablePred (fun j : α => joinIrreducibleCoordinate j) :=
    Classical.decPred _
  let _ : DecidablePred (fun j : α => j ≤ x) := Classical.decPred _
  (Finset.univ.filter joinIrreducibleCoordinate).filter (fun j => j ≤ x)

/-- The join represented by a finite set of coordinates. -/
def coordinateJoin {α : Type*}
    [SemilatticeSup α] [OrderBot α] (S : Finset α) : α :=
  S.sup id

/-- Representation by the join-irreducible coordinates. -/
def joinIrreducibleCoordinateRepresentation {α : Type*}
    [SemilatticeSup α] [OrderBot α] [Fintype α] : Prop :=
  ∀ x : α, coordinateJoin (joinIrreduciblesBelow x) = x

/-- A lower-cover edge in the lattice order. -/
def lowerCover {α : Type*} [PartialOrder α]
    (jStar j : α) : Prop :=
  jStar ≤ j ∧ jStar ≠ j ∧
    ∀ x : α, jStar ≤ x → x ≤ j → x = jStar ∨ x = j

/-- The transported edge profile from the two endpoints of a lower cover. -/
noncomputable def transportedEdge {α : Type*}
    [SemilatticeSup α] [OrderBot α] [Fintype α]
    (jStar j : α) (S : Finset α) : Finset α :=
  let _ : DecidableEq α := Classical.decEq _
  (joinIrreduciblesBelow (j ⊔ coordinateJoin S)) \
    (joinIrreduciblesBelow (jStar ⊔ coordinateJoin S))

/-- The transported lower-cover edge is pure at `S` when the exact profile
of join-irreducibles below its two transported endpoints is `{j}`. -/
def pureTransportedEdge {α : Type*}
    [SemilatticeSup α] [OrderBot α] [Fintype α]
    (jStar j : α) (T S : Finset α) : Prop :=
  joinIrreducibleCoordinateRepresentation (α := α) ∧
    T.card = 3 ∧
    (∀ t ∈ T, joinIrreducibleCoordinate t) ∧
    joinIrreducibleCoordinate j ∧
    j ∉ T ∧
    lowerCover jStar j ∧
    S ⊆ T ∧
    transportedEdge jStar j S = ({j} : Finset α)

end

end MathlibPlus.Open.NewResearch2.R0390AtomisticClosure.Claim20801Repair
