import Mathlib

namespace MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable section

/-- A canonical finite carrier with one new vertex at each successor. -/
def Vertex : ℕ → Type
  | 0 => Empty
  | n + 1 => Vertex n ⊕ Unit

theorem finiteVertexProof : ∀ n, Finite (Vertex n)
  | 0 => by
      change Finite Empty
      infer_instance
  | n + 1 => by
      change Finite (Vertex n ⊕ Unit)
      letI : Finite (Vertex n) := finiteVertexProof n
      infer_instance

instance finiteVertex (n : ℕ) : Finite (Vertex n) := finiteVertexProof n
instance fintypeVertex (n : ℕ) : Fintype (Vertex n) := Fintype.ofFinite (Vertex n)

/-- Finite trees on the canonical carrier of cardinality `n`. -/
abbrev FiniteTree (n : ℕ) := {G : SimpleGraph (Vertex n) // G.IsTree}

def treeIso {n : ℕ} (G H : FiniteTree n) : Prop := Nonempty (G.1 ≃g H.1)

def treeSetoid (n : ℕ) : Setoid (FiniteTree n) where
  r := treeIso
  iseqv := {
    refl := fun G => ⟨SimpleGraph.Iso.refl⟩
    symm := by
      intro G H ⟨e⟩
      exact ⟨e.symm⟩
    trans := by
      intro G H K ⟨e₁⟩ ⟨e₂⟩
      exact ⟨e₂.comp e₁⟩
  }

/-- Unlabelled `n`-vertex finite trees. -/
def UnlabelledTree (n : ℕ) := Quotient (treeSetoid n)

noncomputable def treeRepresentative {n : ℕ} (C : UnlabelledTree n) : FiniteTree n :=
  Quotient.out C

/-- A rooted occurrence is a tree card together with a vertex of its chosen representative. -/
abbrev RootedOccurrence (n : ℕ) := UnlabelledTree n × Vertex n

/-- The graph obtained by grafting a fresh leaf at `v`. -/
def attachGraph {n : ℕ} (G : FiniteTree n) (v : Vertex n) : SimpleGraph (Vertex n.succ) :=
  (G.1 ⊕g (⊥ : SimpleGraph Unit)) ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr ())

lemma attachGraph_isTree {n : ℕ} (G : FiniteTree n) (v : Vertex n) :
    (attachGraph G v).IsTree := by
  classical
  let H : SimpleGraph (Vertex n ⊕ Unit) := G.1 ⊕g (⊥ : SimpleGraph Unit)
  have hconn : (H ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr ())).Connected := by
    dsimp [H]
    exact G.2.connected.sum_sup_edge
      (SimpleGraph.IsTree.of_subsingleton : (⊥ : SimpleGraph Unit).IsTree).connected
  have hHcard : H.edgeFinset.card = G.1.edgeFinset.card := by
    rw [H.edgeFinset_card, G.1.edgeFinset_card]
    rw [Fintype.card_congr SimpleGraph.edgeSetSumEquiv]
    simp
  have hKcard : (H ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr ())).edgeFinset.card =
      G.1.edgeFinset.card + 1 := by
    rw [SimpleGraph.card_edgeFinset_sup_edge]
    · exact congrArg (fun k => k + 1) hHcard
    · simp [H]
    · simp
  change (H ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr ())).IsTree
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · exact hconn
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    rw [SimpleGraph.edgeFinset_card] at hKcard
    rw [hKcard, G.2.card_edgeFinset]
    simp [Fintype.card_sum]

/-- The unlabelled tree obtained by attaching a fresh leaf to a rooted occurrence. -/
noncomputable def attach (C : UnlabelledTree n) (v : Vertex n) : UnlabelledTree n.succ :=
  Quotient.mk (treeSetoid n.succ) ⟨attachGraph (treeRepresentative C) v,
    attachGraph_isTree (treeRepresentative C) v⟩

/-- The attachment map on rooted occurrences. -/
noncomputable def attachmentMap (n : ℕ) : RootedOccurrence n → UnlabelledTree n.succ :=
  fun ⟨C, v⟩ => attach C v

/-- The attachment map indexed by the number of vertices in the target tree. -/
noncomputable def attachmentMapAt (n : ℕ) (h : 1 ≤ n) :
    RootedOccurrence (n - 1) → UnlabelledTree n :=
  (Nat.sub_add_cancel h) ▸ attachmentMap (n - 1)

/-- The rational space freely based by unlabelled `n`-vertex trees. -/
abbrev TreeSpace (n : ℕ) := UnlabelledTree n →₀ ℚ

/-- The direct sum of the rational vertex spaces of all unlabelled `n`-vertex cards. -/
abbrev RootedCardSpace (n : ℕ) := UnlabelledTree n →₀ (Vertex n →₀ ℚ)

/-- The basis vector for a rooted occurrence. -/
def rootedBasis (C : UnlabelledTree n) (v : Vertex n) : RootedCardSpace n :=
  Finsupp.single C (Finsupp.single v 1)

/-- The basis vector for an unlabelled tree. -/
def treeBasis (T : UnlabelledTree n) : TreeSpace n :=
  Finsupp.single T 1

/-- The linearization of leaf attachment. -/
noncomputable def attachmentLinearization (n : ℕ) :
    RootedCardSpace n →ₗ[ℚ] TreeSpace n.succ :=
  Finsupp.lsum ℚ (fun C =>
    Finsupp.linearCombination ℚ (fun v => treeBasis (attach C v)))

/-- The linearization indexed by the number of vertices in the target tree. -/
noncomputable def attachmentLinearizationAt (n : ℕ) (h : 1 ≤ n) :
    RootedCardSpace (n - 1) →ₗ[ℚ] TreeSpace n :=
  (Nat.sub_add_cancel h) ▸ attachmentLinearization (n - 1)

/-- The attachment map sends each rooted basis vector to the corresponding tree basis vector. -/
@[simp] lemma attachmentLinearization_rootedBasis (n : ℕ) (C : UnlabelledTree n)
    (v : Vertex n) :
    attachmentLinearization n (rootedBasis C v) = treeBasis (attach C v) := by
  simp [attachmentLinearization, rootedBasis, treeBasis]

/-- The leaf predicate on a chosen finite-tree representative. -/
def IsLeaf {n : ℕ} (G : FiniteTree n) (v : Vertex n) : Prop :=
  Nat.card (G.1.neighborSet v) = 1

/-- The graph left after deleting a vertex from a chosen representative. -/
def deletionGraph {n : ℕ} (G : FiniteTree n) (v : Vertex n) :
    SimpleGraph {w : Vertex n // w ∈ ({v}ᶜ : Set (Vertex n))} :=
  G.1.induce ({v}ᶜ)

/-- Deleting a leaf from a chosen representative supplies a rooted card. -/
def DeletionSuppliesRootedCard {n : ℕ} (h : 1 ≤ n) (T : UnlabelledTree n) : Prop :=
  ∃ (v : Vertex n) (C : UnlabelledTree (n - 1)) (u : Vertex (n - 1)),
    IsLeaf (treeRepresentative T) v ∧
    (∃ (e : deletionGraph (treeRepresentative T) v ≃g (treeRepresentative C).1)
      (w : Vertex n) (hw : w ∈ ({v}ᶜ : Set (Vertex n))),
      (treeRepresentative T).1.Adj v w ∧ e ⟨w, hw⟩ = u) ∧
    attachmentMapAt n h (C, u) = T

/-- A nontrivial finite tree has a leaf; deleting one supplies a rooted card; consequently
attachment and its rational linearization are surjective. -/
def AttachmentSurjective (n : ℕ) : Prop :=
  ∀ hn : 2 ≤ n,
    let h : 1 ≤ n := by omega
    (∀ T : UnlabelledTree n, DeletionSuppliesRootedCard h T) ∧
    Function.Surjective (attachmentMapAt n h) ∧
    Function.Surjective (attachmentLinearizationAt n h)

end
end MathlibPlus.Open.Combinatorics.TreeAttachment
