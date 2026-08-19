import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1759.Claim34181

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

private def boundaryEdge {V : Type} (Y : SimpleGraph V)
    (C : Finset V) (e : Sym2 V) : Prop :=
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

private def rootedCarrierRow {V : Type} [Fintype V]
    (Y : SimpleGraph V) (_r : V) : Cube V :=
  ∑ A ∈ (edgeUniverse Y).powerset, stateBasis A

/-- Claim 34181: on the complete finite tree edge-state carrier, every
    rooted row is the sum of the complete blocks indexed by nonempty connected
    vertex sets containing the root. -/
def claim34181 : Prop :=
  ∀ {V : Type} [Fintype V]
    (Y : SimpleGraph V), Y.IsTree →
    ∀ r : V, rootedCarrierRow Y r =
      ∑ C ∈ (Finset.univ : Finset (Finset V)).filter (fun C =>
        connectedCarrier Y C ∧ r ∈ C), completeCarrierBlock Y C

end
end MathlibPlus.Open.ResearchFormalization.R1759.Claim34181
