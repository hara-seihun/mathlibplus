import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd

open scoped BigOperators

noncomputable section

/-- A finite graph carried by an arbitrary finite vertex type. -/
def GraphObject := Σ V : Type, Fintype V × SimpleGraph V

/-- Isomorphism of the finite graph objects, used for unlabeled graph types. -/
def graphEquivalent : GraphObject → GraphObject → Prop
  | ⟨V, ⟨_fV, G⟩⟩, ⟨W, ⟨_fW, H⟩⟩ => Nonempty (G ≃g H)

/-- The type of finite unlabeled graph types. -/
abbrev GraphClass := Quot graphEquivalent

/-- The graph type of a finite simple graph. -/
noncomputable def graphClass {V : Type} [Fintype V] (G : SimpleGraph V) : GraphClass :=
  Quot.mk graphEquivalent ⟨V, ⟨inferInstance, G⟩⟩

/-- The graph type of a graph whose finite carrier is supplied by `Finite`. -/
noncomputable def graphClassFinite {V : Type} [Finite V]
    (G : SimpleGraph V) : GraphClass :=
  Quot.mk graphEquivalent ⟨V, ⟨Fintype.ofFinite V, G⟩⟩

/-- Vertex degree in a finite simple graph. -/
def graphDegree14336 {V : Type} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborSet v).ncard

/-- The canonical ordered edge carrier for a graph on `Fin n`. -/
noncomputable def normalizedEdgeSet14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2)

/-- An edge uses a vertex. -/
def edgeUses14336 (e : Fin n × Fin n) (v : Fin n) : Prop :=
  v = e.1 ∨ v = e.2

/-- A finite edge set misses a vertex. -/
def missesVertex14336 {n : ℕ}
    (A : Finset (Fin n × Fin n)) : Prop :=
  ∃ v : Fin n, ∀ e ∈ A, ¬edgeUses14336 e v

/-- The complement of an edge set misses a vertex in the ambient graph. -/
def complementMissesVertex14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n × Fin n)) : Prop :=
  ∃ v : Fin n,
    ∀ e ∈ normalizedEdgeSet14336 G, e ∉ A → ¬edgeUses14336 e v

/-- A valid two-block star row: the first block is a nonempty edge-star in the
ambient graph, and both blocks miss a vertex. -/
def starPairValid14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n × Fin n)) : Prop :=
  A.Nonempty ∧
    A ⊆ normalizedEdgeSet14336 G ∧
    (∃ c : Fin n, ∀ e ∈ A, edgeUses14336 e c) ∧
    missesVertex14336 A ∧
    complementMissesVertex14336 G A

/-- A pendant edge. -/
def pendantEdge14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) : Prop :=
  e ∈ normalizedEdgeSet14336 G ∧
    (graphDegree14336 G e.1 = 1 ∨ graphDegree14336 G e.2 = 1)

/-- A leaf incident to an edge. -/
def leafIncidentTo14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) (v : Fin n) : Prop :=
  graphDegree14336 G v = 1 ∧ edgeUses14336 e v

/-- The vertex carrier of the complementary retained block. -/
def complementaryBlockVertices14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n × Fin n)) : Set (Fin n) :=
  {v | ∃ e ∈ normalizedEdgeSet14336 G, e ∉ A ∧ edgeUses14336 e v}

/-- The graph induced by the edges outside a selected block, with its natural
finite vertex carrier. -/
noncomputable def complementaryBlock14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n × Fin n)) :
    SimpleGraph (complementaryBlockVertices14336 G A) :=
  G.induce (complementaryBlockVertices14336 G A)

/-- The graph obtained by deleting a specified vertex. -/
noncomputable def deletedLeafBlock14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph ({x : Fin n | x ≠ v}) :=
  G.induce {x : Fin n | x ≠ v}

/-- The leaf deck, retaining multiplicity. -/
noncomputable def leafDeck14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) : Multiset GraphClass := by
  classical
  exact Multiset.map
    (fun v : Fin n => graphClassFinite (deletedLeafBlock14336 G v))
    ((Finset.univ.filter
      (fun v : Fin n => graphDegree14336 G v = 1)).1)

/-- The rows whose first block has one edge. -/
noncomputable def treeSingleEdgeRows14336 {n : ℕ}
    (G : SimpleGraph (Fin n)) : Multiset (ℕ × GraphClass) := by
  classical
  exact Multiset.map
    (fun A : Finset (Fin n × Fin n) =>
      (A.card, graphClassFinite (complementaryBlock14336 G A)))
    ((Finset.univ.filter
      (fun A : Finset (Fin n × Fin n) =>
        starPairValid14336 G A ∧ A.card = 1)).1)

/-- The finite set of unlabeled tree types at order `n`. -/
noncomputable def treeTypeSet14336 (n : ℕ) : Finset GraphClass := by
  classical
  exact Finset.univ.image
    (fun T : {G : SimpleGraph (Fin n) // G.IsTree} => graphClassFinite T.1)

/-- The number `t_n` of unlabeled trees on `n` vertices. -/
def treeTypeCount14336 (n : ℕ) : ℕ :=
  (treeTypeSet14336 n).card

/-- The global row index set for singleton-edge tree rows. -/
noncomputable def treeLeafRowIndex14336 (n : ℕ) : Finset (ℕ × GraphClass) := by
  classical
  exact Finset.biUnion
    (Finset.univ : Finset {G : SimpleGraph (Fin n) // G.IsTree})
    (fun T =>
      (Finset.univ.filter
        (fun A : Finset (Fin n × Fin n) =>
          starPairValid14336 T.1 A ∧ A.card = 1)).image
        (fun A =>
          (A.card, graphClassFinite (complementaryBlock14336 T.1 A))))

/-- Claim 14336: in the theorem range, singleton-edge valid star rows of a
finite tree are exactly its pendant-edge rows; their complementary blocks are
leaf-deleted trees, and the resulting row index is the `t_(n-1)` tree-type
index. -/
def claim14336 : Prop := by
  classical
  exact
    ∀ (n : ℕ), 5 ≤ n →
    ∀ (G : SimpleGraph (Fin n)), G.IsTree →
      (∀ A : Finset (Fin n × Fin n),
        (starPairValid14336 G A ∧ A.card = 1) ↔
          ∃ e : Fin n × Fin n,
            A = {e} ∧ pendantEdge14336 G e) ∧
      (∀ e : Fin n × Fin n, pendantEdge14336 G e →
        ∃ v : Fin n,
          leafIncidentTo14336 G e v ∧
          starPairValid14336 G {e} ∧
          (complementaryBlock14336 G {e}).IsTree ∧
          (deletedLeafBlock14336 G v).IsTree ∧
          graphClassFinite (complementaryBlock14336 G {e}) =
            graphClassFinite (deletedLeafBlock14336 G v)) ∧
      treeSingleEdgeRows14336 G =
        Multiset.map (fun c : GraphClass => (1, c)) (leafDeck14336 G) ∧
      treeLeafRowIndex14336 n =
        (treeTypeSet14336 (n - 1)).image
          (fun c : GraphClass => (1, c)) ∧
      (treeLeafRowIndex14336 n).card = treeTypeCount14336 (n - 1)

/-- Labelled graph bases on the fixed vertex sets `[n]`. -/
abbrev LabelledGraph14320 (n : ℕ) := SimpleGraph (Fin n)
abbrev LabelledGraphSpace14320 (n : ℕ) :=
  LabelledGraph14320 n →₀ ℚ

/-- Delete a vertex and relabel the remaining vertices by the increasing
bijection with `[n-1]`. -/
noncomputable def deleteVertex14320 {n : ℕ}
    (G : LabelledGraph14320 n) (v : Fin n) :
    LabelledGraph14320 (n - 1) := by
  classical
  by_cases h : 0 < n
  · have hn : 1 ≤ n := h
    let e : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    let j : Fin ((n - 1) + 1) := Fin.cast e.symm v
    exact
      { Adj := fun a b =>
          G.Adj (Fin.cast e (j.succAbove a)) (Fin.cast e (j.succAbove b))
        symm := ⟨fun a b hab => G.symm.symm _ _ hab⟩
        loopless := ⟨fun a haa => G.loopless.irrefl _ haa⟩ }
  · have hn : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    exact Fin.elim0 v

/-- Degree in the fixed labelled graph. -/
def graphDegree14320 {n : ℕ}
    (G : LabelledGraph14320 n) (v : Fin n) : ℕ :=
  (G.neighborSet v).ncard

/-- The degree-weighted deck on one labelled graph basis vector. -/
noncomputable def degreeWeightedDeckOnBasis14320 {n : ℕ}
    (G : LabelledGraph14320 n) : LabelledGraphSpace14320 (n - 1) := by
  classical
  exact ∑ v : Fin n,
    (graphDegree14320 G v : ℚ) •
      Finsupp.single (deleteVertex14320 G v) 1

/-- The linear extension of the displayed degree-weighted deck expression. -/
noncomputable def degreeWeightedDeck14320 (n : ℕ)
    (x : LabelledGraphSpace14320 n) : LabelledGraphSpace14320 (n - 1) :=
  x.sum (fun G a => a • degreeWeightedDeckOnBasis14320 G)

/-- Claim 19920: on the fixed labelled graph basis, the degree-weighted deck
sends `[G]` to the stated degree-weighted sum of the labelled cards `[G-v]`. -/
def claim19920 : Prop :=
  ∀ (n : ℕ) (G : LabelledGraph14320 n),
    degreeWeightedDeck14320 n (Finsupp.single G 1) =
      ∑ v : Fin n,
        (graphDegree14320 G v : ℚ) •
          Finsupp.single (deleteVertex14320 G v) 1

end

end MathlibPlus.Open.ResearchFormalization.GraphClaims01a00bdd
