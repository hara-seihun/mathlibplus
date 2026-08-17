import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped Pointwise

private def quotientCoordinate53446
    {G : Type*} [CommGroup G] (P : Subgroup G) (x : G) : G ⧸ P :=
  QuotientGroup.mk' P x

private abbrev cosetFiber53446
    {G : Type*} [CommGroup G] (P : Subgroup G) (q : G ⧸ P) :=
  {x : G // quotientCoordinate53446 P x = q}

private def openTwinFree53446
    {Q : Type*} (barGraph : SimpleGraph Q) : Prop :=
  ∀ q q', (∀ z, barGraph.Adj q z ↔ barGraph.Adj q' z) → q = q'

private def closedTwinFree53446
    {Q : Type*} (barGraph : SimpleGraph Q) : Prop :=
  ∀ q q',
    (∀ z, (z = q ∨ barGraph.Adj q z) ↔
      (z = q' ∨ barGraph.Adj q' z)) → q = q'

private def canonicalTwinBlowup53446
    {G : Type*} [Fintype G] [CommGroup G]
    (P : Subgroup G) (Sbar : Set (G ⧸ P))
    (barGraph : SimpleGraph (G ⧸ P))
    (graph : SimpleGraph G) (complete : Bool) : Prop :=
  barGraph = SimpleGraph.mulCayley Sbar ∧
    (1 : G ⧸ P) ∉ Sbar ∧
    Sbar = Sbar⁻¹ ∧
    (complete = true → closedTwinFree53446 barGraph) ∧
    (complete ≠ true → openTwinFree53446 barGraph) ∧
    (∀ x y,
      graph.Adj x y ↔
        if complete then
          (quotientCoordinate53446 P x = quotientCoordinate53446 P y ∧ x ≠ y) ∨
            barGraph.Adj (quotientCoordinate53446 P x)
              (quotientCoordinate53446 P y)
        else
          barGraph.Adj (quotientCoordinate53446 P x)
            (quotientCoordinate53446 P y))

private def wreathBaseMember53446
    {G : Type*} [CommGroup G]
    (P : Subgroup G) (e : Equiv.Perm G) : Prop :=
  ∀ x : G, quotientCoordinate53446 P (e x) = quotientCoordinate53446 P x

private def regularPermutationSubgroup53446
    {V : Type*} (R : Subgroup (Equiv.Perm V)) : Prop :=
  ∀ x y : V, ∃! r : R, r.1 x = y

private def graphAutomorphismMember53446
    {V : Type*} (graph : SimpleGraph V) (e : Equiv.Perm V) : Prop :=
  ∀ x y, graph.Adj x y ↔ graph.Adj (e x) (e y)

/-- Claim 53446: for a regular subgroup isomorphic to the abelian Cayley
    group, the quotient image and the fibre kernel have the stated orders,
    and the kernel is regular on every canonical fibre. -/
def canonicalTwinWreathRegularKernel53446 : Prop :=
  ∀ {G : Type*} [Fintype G] [CommGroup G]
    (P : Subgroup G) (Sbar : Set (G ⧸ P))
    (barGraph : SimpleGraph (G ⧸ P)) (graph : SimpleGraph G)
    (complete : Bool),
    canonicalTwinBlowup53446 P Sbar barGraph graph complete →
      ∀ R : Subgroup (Equiv.Perm G),
        (∀ r : R, graphAutomorphismMember53446 graph r.1) →
        regularPermutationSubgroup53446 R →
        Nonempty (R ≃* G) →
        ∀ π : R →* Equiv.Perm (G ⧸ P),
          (∀ r : R, ∀ x : G,
            quotientCoordinate53446 P (r.1 x) =
              π r (quotientCoordinate53446 P x)) →
          let B : Set (Equiv.Perm G) :=
            {e | wreathBaseMember53446 P e}
          let K := {r : R // (r.1 : Equiv.Perm G) ∈ B}
          (∀ a b : Set.range π, a.1 * b.1 = b.1 * a.1) ∧
          (∀ q q' : G ⧸ P, ∃ a : Set.range π, a.1 q = q') ∧
          (∀ q q' : G ⧸ P, ∃! a : Set.range π, a.1 q = q') ∧
          Nat.card (Set.range π) = Nat.card (G ⧸ P) ∧
          Nat.card K = Nat.card P ∧
          (∀ q : G ⧸ P, ∀ x y : cosetFiber53446 P q,
            ∃! r : K, r.1.1 x.1 = y.1)

end MathlibPlus.Open.ResearchFormalization
