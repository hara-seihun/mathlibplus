import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R1759Claim34185

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

private def internalEdge {V : Type}
    (Y : SimpleGraph V) (C : Finset V) (e : Sym2 V) : Prop :=
  edgeWith e (fun v w => v ∈ C ∧ w ∈ C ∧ Y.Adj v w)

private def boundaryEdge {V : Type}
    (Y : SimpleGraph V) (C : Finset V) (e : Sym2 V) : Prop :=
  edgeWith e (fun v w =>
    (v ∈ C ∧ w ∉ C ∨ v ∉ C ∧ w ∈ C) ∧ Y.Adj v w)

private def completeCarrierStates {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset (EdgeState V) :=
  (edgeUniverse Y).powerset.filter (fun A =>
    (∀ e, internalEdge Y C e → e ∈ A) ∧
      (∀ e, boundaryEdge Y C e → e ∉ A))

private def stateBasis {V : Type} (A : EdgeState V) : Cube V :=
  Finsupp.single A 1

private def completeCarrierBlock {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Cube V :=
  ∑ A ∈ completeCarrierStates Y C, stateBasis A

private def connectedCarrier {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Prop :=
  C.Nonempty ∧ (Y.induce (C : Set V)).Connected

private def completionStates {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset (EdgeState V) :=
  (edgeUniverse Y).powerset.filter (fun A =>
    ∀ e, internalEdge Y C e → e ∈ A)

private def absorptionCompletion {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Cube V :=
  ∑ A ∈ completionStates Y C, stateBasis A

private def boundaryVertices {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter (fun v =>
    v ∉ C ∧ ∃ u ∈ C, Y.Adj u v)

/-- Claim 34185: the absorption-completion inverse is supported on the
immediate outside vertex boundary of a connected carrier. -/
def boundaryLocalMobiusInverse_claim34185 : Prop :=
  ∀ {V : Type} [Fintype V]
    (Y : SimpleGraph V), Y.IsTree →
    ∀ C : Finset V, connectedCarrier Y C →
      completeCarrierBlock Y C =
        ∑ S ∈ (boundaryVertices Y C).powerset,
          ((-1 : ℤ) ^ S.card) • absorptionCompletion Y (C ∪ S)

end

end MathlibPlus.Open.ResearchFormalization.R1759Claim34185
