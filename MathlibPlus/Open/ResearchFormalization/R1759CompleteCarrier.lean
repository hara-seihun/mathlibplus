import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1759

noncomputable section

abbrev Record1759EdgeState (V : Type) := Finset (Sym2 V)

def record1759EdgeUniverse {V : Type} [Fintype V]
    (Y : SimpleGraph V) : Record1759EdgeState V :=
  Y.edgeSet.toFinite.toFinset

def record1759EdgeWith {V : Type} (e : Sym2 V)
    (P : V → V → Prop) : Prop :=
  ∃ v w, e = s(v, w) ∧ P v w

def record1759InternalEdge {V : Type}
    (Y : SimpleGraph V) (C : Finset V) (e : Sym2 V) : Prop :=
  record1759EdgeWith e (fun v w =>
    v ∈ C ∧ w ∈ C ∧ Y.Adj v w)

def record1759BoundaryEdge {V : Type}
    (Y : SimpleGraph V) (C : Finset V) (e : Sym2 V) : Prop :=
  record1759EdgeWith e (fun v w =>
    (v ∈ C ∧ w ∉ C ∨ v ∉ C ∧ w ∈ C) ∧ Y.Adj v w)

def record1759OutsideEdge {V : Type}
    (Y : SimpleGraph V) (C : Finset V) (e : Sym2 V) : Prop :=
  record1759EdgeWith e (fun v w =>
    v ∉ C ∧ w ∉ C ∧ Y.Adj v w)

/-- The complete carrier block, viewed as its exact set of edge states. -/
def record1759CompleteCarrierBlock {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) :
    Set (Record1759EdgeState V) :=
  {A | A ∈ (record1759EdgeUniverse Y).powerset ∧
    (∀ e, record1759InternalEdge Y C e → e ∈ A) ∧
    (∀ e, record1759BoundaryEdge Y C e → e ∉ A)}

/-- The Boolean edge-subset cube written with the three source conditions:
internal edges are selected, boundary edges are absent, and no condition is
placed on complement edges. -/
def record1759BooleanEdgeSubsetCube {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) :
    Set (Record1759EdgeState V) :=
  {A | A ⊆ record1759EdgeUniverse Y ∧
    (∀ e, record1759InternalEdge Y C e → e ∈ A) ∧
    (∀ e, record1759BoundaryEdge Y C e → e ∉ A)}

def record1759ConnectedCarrier {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Prop :=
  C.Nonempty ∧ (Y.induce (C : Set V)).Connected

/-- Claim 34179: for a tree and a nonempty connected carrier, the complete
carrier block is precisely the Boolean cube with forced internal edges,
forbidden boundary edges, and arbitrary complement edges. -/
def completeCarrierBooleanCube_claim34179 : Prop :=
  ∀ {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V),
    Y.IsTree → record1759ConnectedCarrier Y C →
      record1759CompleteCarrierBlock Y C =
        record1759BooleanEdgeSubsetCube Y C

end

end MathlibPlus.Open.ResearchFormalization.R1759
