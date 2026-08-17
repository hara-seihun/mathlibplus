import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped Pointwise

private def quotientCoordinate53445
    {G : Type*} [CommGroup G] (P : Subgroup G) (x : G) : G ⧸ P :=
  QuotientGroup.mk' P x

private abbrev cosetFiber53445
    {G : Type*} [CommGroup G] (P : Subgroup G) (q : G ⧸ P) :=
  {x : G // quotientCoordinate53445 P x = q}

private def quotientGraphAutomorphism53445
    {Q : Type*} (barGraph : SimpleGraph Q) (σ : Equiv.Perm Q) : Prop :=
  ∀ q q', barGraph.Adj q q' ↔ barGraph.Adj (σ q) (σ q')

private def openTwinFree53445
    {Q : Type*} (barGraph : SimpleGraph Q) : Prop :=
  ∀ q q', (∀ z, barGraph.Adj q z ↔ barGraph.Adj q' z) → q = q'

private def closedTwinFree53445
    {Q : Type*} (barGraph : SimpleGraph Q) : Prop :=
  ∀ q q',
    (∀ z, (z = q ∨ barGraph.Adj q z) ↔
      (z = q' ∨ barGraph.Adj q' z)) → q = q'

private def canonicalTwinBlowup53445
    {G : Type*} [Fintype G] [CommGroup G]
    (P : Subgroup G) (Sbar : Set (G ⧸ P))
    (barGraph : SimpleGraph (G ⧸ P))
    (graph : SimpleGraph G) (complete : Bool) : Prop :=
  barGraph = SimpleGraph.mulCayley Sbar ∧
    (1 : G ⧸ P) ∉ Sbar ∧
    Sbar = Sbar⁻¹ ∧
    (complete = true → closedTwinFree53445 barGraph) ∧
    (complete ≠ true → openTwinFree53445 barGraph) ∧
    (∀ x y,
      graph.Adj x y ↔
        if complete then
          (quotientCoordinate53445 P x = quotientCoordinate53445 P y ∧ x ≠ y) ∨
            barGraph.Adj (quotientCoordinate53445 P x)
              (quotientCoordinate53445 P y)
        else
          barGraph.Adj (quotientCoordinate53445 P x)
            (quotientCoordinate53445 P y))

private def graphAutomorphismSet53445
    {V : Type*} (graph : SimpleGraph V) : Set (Equiv.Perm V) :=
  {e | ∀ x y, graph.Adj x y ↔ graph.Adj (e x) (e y)}

private def wreathMember53445
    {G : Type*} [Fintype G] [CommGroup G]
    (P : Subgroup G) (barGraph : SimpleGraph (G ⧸ P))
    (e : Equiv.Perm G) : Prop :=
  ∃ σ : Equiv.Perm (G ⧸ P),
    quotientGraphAutomorphism53445 barGraph σ ∧
      ∃ ρ : ∀ q : G ⧸ P,
          cosetFiber53445 P q ≃ cosetFiber53445 P (σ q),
        ∀ (x : G)
          (hx : quotientCoordinate53445 P x = quotientCoordinate53445 P x),
          e x =
            (ρ (quotientCoordinate53445 P x)
              ⟨x, hx⟩).1

/-- Claim 53445: on a canonical complete- or independent-fibre blow-up,
    graph automorphisms are exactly quotient automorphisms together with
    independent permutations of the canonical coset fibres. -/
def canonicalTwinWreathAutomorphismStructure53445 : Prop :=
  ∀ {G : Type*} [Fintype G] [CommGroup G]
    (P : Subgroup G) (Sbar : Set (G ⧸ P))
    (barGraph : SimpleGraph (G ⧸ P)) (graph : SimpleGraph G)
    (complete : Bool),
    canonicalTwinBlowup53445 P Sbar barGraph graph complete →
      graphAutomorphismSet53445 graph =
        {e | wreathMember53445 P barGraph e}

end MathlibPlus.Open.ResearchFormalization
