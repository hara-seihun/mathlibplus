import Mathlib

<<<<<<< ours
namespace MathlibPlus.Open.Research.FormalizationBatch019ffedf

/-- The matching relation between the two clique components. -/
def twoCliqueRelation (a d k : ℕ) (x y : Fin a ⊕ Fin d) : Prop :=
  match x, y with
  | Sum.inl _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => True
  | Sum.inl i, Sum.inr j => i.1 = j.1 ∧ i.1 < k
  | Sum.inr j, Sum.inl i => i.1 = j.1 ∧ i.1 < k

/-- `L(a,d,k)`: two disjoint cliques with a size-`k` matching between them. -/
def L (a d k : ℕ) : SimpleGraph (Fin a ⊕ Fin d) :=
  SimpleGraph.fromRel (twoCliqueRelation a d k)

/-- Graph isomorphism written as a vertex equivalence preserving adjacency. -/
def GraphIso {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  ∃ e : α ≃ β, ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y)

/-- The graph obtained by deleting one vertex. -/
def deleteVertex {α : Type} (G : SimpleGraph α) (u : α) : SimpleGraph {x : α // x ≠ u} :=
  G.induce {x | x ≠ u}

/-- The number of edges of a finite simple graph. -/
noncomputable def edgeCount {α : Type} [Fintype α] (G : SimpleGraph α) : ℕ :=
  G.edgeSet.ncard

def H (c b : ℕ) : SimpleGraph (Fin (c + 1) ⊕ Fin (c - 1)) := L (c + 1) (c - 1) b

def A (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin (c - 1)) := L c (c - 1) (b - 1)

def B (c b : ℕ) : SimpleGraph (Fin c ⊕ Fin (c - 1)) := L c (c - 1) b

def E (c b : ℕ) : SimpleGraph (Fin (c + 1) ⊕ Fin (c - 2)) := L (c + 1) (c - 2) (b - 1)

/-- Claim 26552. -/
def claim26552 : Prop :=
  ∀ (c b : ℕ), c ≥ 3 → 2 ≤ b → b ≤ c - 1 →
    edgeCount (B c b) = edgeCount (A c b) + 1 ∧
    edgeCount (E c b) = edgeCount (A c b) + 2 ∧
    ¬ GraphIso (A c b) (B c b) ∧
    ¬ GraphIso (A c b) (E c b) ∧
    ¬ GraphIso (B c b) (E c b)

/-- Claim 26555. -/
def claim26555 : Prop :=
  ∀ (c b : ℕ), c ≥ 3 → 2 ≤ b → b ≤ c - 1 →
    ∀ {V : Type} [Fintype V] (X : SimpleGraph V) (u v w : V),
      u ≠ v → u ≠ w → v ≠ w →
      GraphIso (deleteVertex X u) (A c b) →
      GraphIso (deleteVertex X v) (B c b) →
      GraphIso (deleteVertex X w) (E c b) →
      GraphIso X (H c b)

end MathlibPlus.Open.Research.FormalizationBatch019ffedf
=======
namespace MathlibPlus.Open.Research.FormalizationBatch

noncomputable section

open scoped BigOperators

def SpanningEdgeState {V : Type*} (G : SimpleGraph V) := {A : SimpleGraph V // A ≤ G}

noncomputable def componentSupport {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : G.ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => G.connectedComponentMk v = C)

noncomputable def componentOrder {V : Type*} [Fintype V]
    (G : SimpleGraph V) (C : G.ConnectedComponent) : ℕ := by
  classical
  exact Fintype.card {v : V // G.connectedComponentMk v = C}

def componentOrderOccurrence {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :=
  {C : G.ConnectedComponent // componentOrder G C = k}

noncomputable def componentOrderProfile {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Multiset ℕ := by
  classical
  exact (Finset.univ : Finset G.ConnectedComponent).val.map (componentOrder G)

noncomputable def componentProfileMultiplicity {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact (componentOrderProfile G).count k

noncomputable def componentOccurrenceCard {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun C : G.ConnectedComponent =>
    componentOrder G C = k)).card

noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  G.edgeFinset.card

noncomputable def componentCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Fintype.card G.ConnectedComponent

structure MarkedComponentState {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) where
  state : SpanningEdgeState G
  component : state.1.ConnectedComponent
  order_eq : componentOrder state.1 component = k

noncomputable def deletedComplement {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : SimpleGraph {v : V // v ∉ (↑S : Set V)} :=
  T.induce ((↑S : Set V)ᶜ)

noncomputable def supportGraph {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : SimpleGraph {v : V // v ∈ (↑S : Set V)} :=
  T.induce (↑S : Set V)

noncomputable def deletedComponentCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  letI : Fintype {v : V // v ∉ (↑S : Set V)} := Fintype.ofFinite _
  exact componentCount (deletedComplement T S)

structure DeletionData {V : Type*} [Fintype V]
    (T : SimpleGraph V) (k : ℕ) where
  support : Finset V
  nonempty : support.Nonempty
  cardinality : support.card = k
  connected : (supportGraph T support).Preconnected
  complementState : SpanningEdgeState (deletedComplement T support)

noncomputable def restrictState {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (A : SpanningEdgeState T) :
    SpanningEdgeState (deletedComplement T S) := by
  refine ⟨A.1.induce ((↑S : Set V)ᶜ), ?_⟩
  intro u v huv
  exact A.2 huv

noncomputable def boundaryCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : V × V =>
    p.1 ∈ (↑S : Set V) ∧ p.2 ∉ (↑S : Set V) ∧ T.Adj p.1 p.2)).card

noncomputable def attachmentCount {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V)
    (C : (deletedComplement T S).ConnectedComponent) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : V × V =>
    ∃ hs : p.1 ∈ (↑S : Set V), ∃ ho : p.2 ∉ (↑S : Set V),
      T.Adj p.1 p.2 ∧
        (deletedComplement T S).connectedComponentMk ⟨p.2, ho⟩ = C)).card

def claim26061 : Prop :=
  ∀ (p : ℕ →₀ ℕ) (k : ℕ),
    0 < k →
    (MvPolynomial.pderiv k) (MvPolynomial.monomial p (1 : ℤ)) =
      ∑ _ : Fin (p k),
        MvPolynomial.monomial (p - Finsupp.single k 1) (1 : ℤ)

def claim26059 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A : SpanningEdgeState G) (k : ℕ),
    0 < k →
      componentProfileMultiplicity A.1 k = componentOccurrenceCard A.1 k

def claim26062 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A : SpanningEdgeState G) (k : ℕ),
    0 < k →
    (componentProfileMultiplicity A.1 k = componentOccurrenceCard A.1 k) ∧
    (∀ C : A.1.ConnectedComponent,
      componentOrder A.1 C = k ↔
        (componentSupport A.1 C).card = k)

def internalEdgesPresent {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (A : SpanningEdgeState T) : Prop :=
  ∀ u v : V, u ∈ (↑S : Set V) → v ∈ (↑S : Set V) →
    T.Adj u v → A.1.Adj u v

def boundaryEdgesAbsentIn {V : Type*} [Fintype V]
    (T : SimpleGraph V) (S : Finset V) (A : SpanningEdgeState T) : Prop :=
  ∀ u v : V, u ∈ (↑S : Set V) → v ∉ (↑S : Set V) → ¬ A.1.Adj u v

def claim26063 : Prop :=
  ∀ {V : Type*} [Fintype V] (T : SimpleGraph V) (k : ℕ),
    0 < k → T.IsTree →
    ∃ e : MarkedComponentState T k ≃ DeletionData T k,
      (∀ m, (e m).support = componentSupport m.state.1 m.component ∧
        (e m).complementState =
          restrictState T (e m).support m.state) ∧
      (∀ d, let m := e.symm d; componentSupport m.state.1 m.component = d.support ∧
        internalEdgesPresent T d.support m.state ∧
        boundaryEdgesAbsentIn T d.support m.state ∧
        restrictState T d.support m.state = d.complementState)

def claim26074 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (A : SpanningEdgeState G),
    G.IsAcyclic →
      edgeCount A.1 + componentCount A.1 = Fintype.card V

def claim26075 : Prop :=
  ∀ {V : Type*} [Fintype V] (T : SimpleGraph V) (S : Finset V),
    T.IsTree →
    S.Nonempty →
    (supportGraph T S).Preconnected →
    (∀ C : (deletedComplement T S).ConnectedComponent,
      attachmentCount T S C = 1) ∧
    deletedComponentCount T S = boundaryCount T S

end
end MathlibPlus.Open.Research.FormalizationBatch
>>>>>>> theirs
