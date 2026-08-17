import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1759Claim34186

noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

private abbrev EdgeState (V : Type) := Finset (Sym2 V)
private abbrev Cube (V : Type) := EdgeState V →₀ ℤ
private abbrev XPoly := MvPolynomial ℕ ℚ
private abbrev ZPoly := Polynomial XPoly

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

private def outsideEdge {V : Type} (Y : SimpleGraph V)
    (C : Finset V) (e : Sym2 V) : Prop :=
  edgeWith e (fun v w => v ∉ C ∧ w ∉ C ∧ Y.Adj v w)

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

private def completionStates {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset (EdgeState V) :=
  (edgeUniverse Y).powerset.filter (fun A =>
    ∀ e, internalEdge Y C e → e ∈ A)

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

private def boundaryVertices {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : Finset V :=
  (Finset.univ : Finset V).filter (fun v =>
    v ∉ C ∧ ∃ u ∈ C, Y.Adj u v)

private def outsideGraph {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) :
    SimpleGraph {v : V // v ∉ C} :=
  SimpleGraph.fromRel (fun u v => Y.Adj u v)

private def selectedOutsideGraph {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) (A : EdgeState V) :
    SimpleGraph {v : V // v ∉ C} :=
  SimpleGraph.fromRel (fun u v =>
    Y.Adj u v ∧ s((u : V), (v : V)) ∈ A)

private def outsideMonomial {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) (A : EdgeState V) : XPoly :=
  ∏ K : (selectedOutsideGraph Y C A).ConnectedComponent,
    MvPolynomial.X (Set.ncard K.supp)

private noncomputable def outsideU {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : XPoly :=
  MvPolynomial.map (Int.castRingHom ℚ)
    (MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
      (outsideGraph Y C))

private def scalarizedBlock {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : ZPoly :=
  ∑ A ∈ completeCarrierStates Y C,
    Polynomial.X ^ (C.card - 1) * Polynomial.C (outsideMonomial Y C A)

private def scalarizedCompletion {V : Type} [Fintype V]
    (Y : SimpleGraph V) (C : Finset V) : ZPoly :=
  Polynomial.X ^ (C.card - 1) * Polynomial.C (outsideU Y C)

private def strictLowerHost {V : Type} [Fintype V]
    (C : Finset V) : Prop :=
  2 ≤ C.card → Fintype.card V - C.card + 1 < Fintype.card V

/-- Claim 34186: every term indexed by the immediate boundary in the
boundary-local inverse is the scalarization of a contracted complete rooted
row, and a nonsingleton carrier gives a strict lower host. -/
def scalarTermsDescendToStrictLowerHosts_claim34186 : Prop :=
  ∀ {V : Type} [Fintype V]
    (Y : SimpleGraph V), Y.IsTree →
    ∀ C : Finset V, connectedCarrier Y C → 2 ≤ C.card →
      ∀ S ∈ (boundaryVertices Y C).powerset,
        C ⊆ C ∪ S ∧
          connectedCarrier Y (C ∪ S) ∧
            absorptionCompletion Y (C ∪ S) =
              contractionCompletion Y (C ∪ S) ∧
              scalarizedBlock Y (C ∪ S) =
                scalarizedCompletion Y (C ∪ S) ∧
                strictLowerHost (C ∪ S)

end

end MathlibPlus.Open.ResearchFormalization.R1759Claim34186
