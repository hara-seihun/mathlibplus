import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1759

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev EdgeState (V : Type) := Finset (Sym2 V)
private abbrev Cube (V : Type) := EdgeState V →₀ ℤ

private def edgeUniverse {V : Type} [Fintype V]
    (Y : SimpleGraph V) : EdgeState V :=
  Y.edgeSet.toFinite.toFinset

private def edgeWith {V : Type} (e : Sym2 V)
    (P : V → V → Prop) : Prop :=
  ∃ v w, e = s(v, w) ∧ P v w

private def internalEdge {V : Type} (Y : SimpleGraph V)
    (C : Finset V) (e : Sym2 V) : Prop :=
  edgeWith e (fun v w => v ∈ C ∧ w ∈ C ∧ Y.Adj v w)

private def connectedCarrier {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Prop :=
  C.Nonempty ∧ (Y.induce (C : Set V)).Connected

private def completionStates {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset (EdgeState V) :=
  (edgeUniverse Y).powerset.filter (fun A =>
    ∀ e, internalEdge Y C e → e ∈ A)

private def stateBasis {V : Type} (A : EdgeState V) : Cube V :=
  Finsupp.single A 1

/-- The completion obtained by forcing internal carrier edges and allowing all
other complement and boundary edge choices. -/
private def absorptionCompletion {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Cube V :=
  ∑ A ∈ completionStates Y C, stateBasis A

private abbrev ContractVertex (V : Type) (C : Finset V) :=
  {v : V // v ∉ C} ⊕ Unit

private def contractVertex {V : Type} (C : Finset V) (v : V) : ContractVertex V C :=
  if h : v ∈ C then Sum.inr () else Sum.inl ⟨v, h⟩

private def contractEdge {V : Type} (C : Finset V)
    (e : Sym2 V) : Sym2 (ContractVertex V C) :=
  Sym2.map (contractVertex C) e

private def contractedGraph {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : SimpleGraph (ContractVertex V C) :=
  SimpleGraph.fromRel (fun a b =>
    ∃ e ∈ edgeUniverse Y,
      contractEdge C e = s(a, b))

private def rootedCarrierRow {V : Type} [Fintype V]
    (Y : SimpleGraph V) (_r : V) : Cube V :=
  ∑ A ∈ (edgeUniverse Y).powerset, stateBasis A

private def liftState {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V)
    (A : EdgeState (ContractVertex V C)) : EdgeState V :=
  (edgeUniverse Y).filter (fun e =>
    internalEdge Y C e ∨ contractEdge C e ∈ A)

private def liftCube {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V)
    (x : Cube (ContractVertex V C)) : Cube V :=
  ∑ A ∈ (edgeUniverse (contractedGraph Y C)).powerset,
    (x A) • stateBasis (liftState Y C A)

private def contractionCompletion {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Cube V :=
  liftCube Y C (rootedCarrierRow (contractedGraph Y C) (Sum.inr ()))

/-- Claim 34183: the exact connected-carrier completion equals the lift of the
complete rooted row after contracting the carrier to one root. -/
def claim34183 : Prop :=
  ∀ {V : Type} [Fintype V]
    (Y : SimpleGraph V), Y.IsTree →
    ∀ C : Finset V,
      connectedCarrier Y C →
        absorptionCompletion Y C = contractionCompletion Y C

end
end MathlibPlus.Open.ResearchFormalization.R1759
