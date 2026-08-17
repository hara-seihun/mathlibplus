import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.FixedSupportClaim26067

noncomputable section

/-- A spanning edge state is a finite edge subset of the host graph. -/
abbrev EdgeState {V : Type*} (G : SimpleGraph V) :=
  {A : Finset (Sym2 V) // ∀ e ∈ A, e ∈ G.edgeSet}

/-- The graph carried by a spanning edge state, on the full host vertex set. -/
def stateGraph {V : Type*} [Fintype V] {G : SimpleGraph V}
    (A : EdgeState G) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (A.1 : Set (Sym2 V))

/-- The order of a connected component in a finite spanning state. -/
def componentOrder {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : G.ConnectedComponent) : ℕ :=
  Nat.card {v : V // G.connectedComponentMk v = C}

/-- The realized vertex support of a connected component. -/
def componentSupport {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : G.ConnectedComponent) : Set V :=
  {v | G.connectedComponentMk v = C}

/-- The finitely supported component-order profile. -/
def componentProfile {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ →₀ ℕ :=
  ∑ C : G.ConnectedComponent,
    (Finsupp.single (componentOrder G C) 1 : ℕ →₀ ℕ)

/-- The monomial attached to a component-order profile. -/
def componentProfileMonomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℤ :=
  MvPolynomial.monomial (componentProfile G) 1

/-- Stanley's component-profile polynomial, with state coefficient `(-1)^|A|`. -/
def stanleyComponentPolynomial {V : Type*} [Fintype V]
    (G : SimpleGraph V) : MvPolynomial ℕ ℤ := by
  classical
  letI : Fintype (EdgeState G) := Fintype.ofFinite _
  exact ∑ A : EdgeState G,
    ((-1 : ℤ) ^ A.1.card) • componentProfileMonomial (stateGraph A)

/-- The spanning graph on the complement of a selected support. -/
def deletedGraph {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∉ (S : Set V)} :=
  T.induce ((S : Set V)ᶜ)

/-- All host edges whose two endpoints lie in the selected support. -/
def internalEdgeCarrier {V : Type*} [Fintype V]
    (S : Finset V) : Set (Sym2 V) :=
  Sym2.fromRel (⟨fun u v h => ⟨h.2, h.1⟩⟩ :
    Std.Symm (fun u v : V => u ∈ S ∧ v ∈ S))

/-- All host edges crossing from the selected support to its complement. -/
def boundaryEdgeCarrier {V : Type*} [Fintype V]
    (S : Finset V) : Set (Sym2 V) :=
  Sym2.fromRel (⟨fun u v h =>
    h.elim (fun h' => Or.inr ⟨h'.2, h'.1⟩)
      (fun h' => Or.inl ⟨h'.2, h'.1⟩)⟩ :
    Std.Symm (fun u v : V =>
      (u ∈ S ∧ v ∉ (S : Set V)) ∨
        (u ∉ (S : Set V) ∧ v ∈ S)))

/-- The finite host edge set, expressed without a graph-specific edge-count API. -/
def hostEdgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ G.edgeSet)

/-- The forced internal edges of the selected support. -/
def internalEdges {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact (hostEdgeFinset T).filter (fun e => e ∈ internalEdgeCarrier S)

/-- Lift a residual edge state on the deleted vertex carrier back to the host. -/
def liftResidual {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V)
    (R : EdgeState (deletedGraph T S)) : Finset (Sym2 V) := by
  classical
  exact R.1.image (Sym2.map (fun v : {v : V // v ∉ (S : Set V)} => (v : V)))

/-- Reconstruct the host edge set from the forced internal part and a residual state. -/
def reconstructedEdges {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V)
    (R : EdgeState (deletedGraph T S)) : Finset (Sym2 V) := by
  classical
  exact internalEdges T S ∪ liftResidual T S R

/-- Stanley's component polynomial on the deleted vertex carrier. -/
def deletedStanleyPolynomial {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : MvPolynomial ℕ ℤ := by
  classical
  letI : Fintype {v : V // v ∉ (S : Set V)} := Fintype.ofFinite _
  exact stanleyComponentPolynomial (deletedGraph T S)

/-- A literal marked order-`k` component whose realized support is `S`. -/
def markedComponentSupport {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (k : ℕ)
    (A : EdgeState T) : Prop :=
  ∃ C : (stateGraph A).ConnectedComponent,
    componentSupport (stateGraph A) C = (S : Set V) ∧
      componentOrder (stateGraph A) C = k

/-- Existence of a marked occurrence with this fixed support. -/
def supportOccurrence {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∃ A : EdgeState T, markedComponentSupport T S k A

/-- The fixed-support contribution after the marked component is removed. -/
def fixedSupportContribution {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (k : ℕ) :
    MvPolynomial ℕ ℤ := by
  classical
  letI : Fintype {v : V // v ∉ (S : Set V)} := Fintype.ofFinite _
  letI : Fintype (EdgeState (deletedGraph T S)) := Fintype.ofFinite _
  exact ∑ R : EdgeState (deletedGraph T S),
    ((-1 : ℤ) ^ (k - 1 + R.1.card)) •
      componentProfileMonomial (stateGraph R)

/-- Claim 26067: fixed support, forced internal and boundary edges, arbitrary
residual states on the deleted tree, and the exact signed Stanley contribution. -/
def claim26067 : Prop :=
  ∀ {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (k : ℕ),
    T.IsTree → S.card = k → 0 < k →
      (supportOccurrence T S k ↔
        (T.induce (S : Set V)).Preconnected) ∧
      (∀ A : EdgeState T,
        markedComponentSupport T S k A →
          (∀ u v : V, u ∈ (S : Set V) → v ∈ (S : Set V) →
            T.Adj u v → Sym2.mk u v ∈ A.1) ∧
          (internalEdges T S).card = k - 1 ∧
          (∀ u v : V, u ∈ (S : Set V) → v ∉ (S : Set V) →
            T.Adj u v → Sym2.mk u v ∉ A.1) ∧
          (∃ R : EdgeState (deletedGraph T S),
            A.1 = reconstructedEdges T S R)) ∧
      (∀ R : EdgeState (deletedGraph T S),
        ∃ A : EdgeState T,
          A.1 = reconstructedEdges T S R ∧
            markedComponentSupport T S k A) ∧
      fixedSupportContribution T S k =
        ((-1 : ℤ) ^ (k - 1)) •
          deletedStanleyPolynomial T S

end
end MathlibPlus.Open.Combinatorics.FixedSupportClaim26067
