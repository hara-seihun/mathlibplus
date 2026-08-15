import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- A labelled presentation of an unlabelled finite tree. -/
def TreeRep (n : ℕ) := {G : SimpleGraph (Fin n) // G.IsTree}

/-- Isomorphism of two fixed-size tree presentations. -/
def treeIso (n : ℕ) (G H : TreeRep n) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ u v, G.1.Adj u v ↔ H.1.Adj (e u) (e v)

def treeSetoid (n : ℕ) : Setoid (TreeRep n) where
  r := treeIso n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro G
      exact ⟨Equiv.refl _, by simp⟩
    · intro G H h
      rcases h with ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      intro u v
      simpa using (he (e.symm u) (e.symm v)).symm
    · intro G H K hGH hHK
      rcases hGH with ⟨e, he⟩
      rcases hHK with ⟨f, hf⟩
      refine ⟨e.trans f, ?_⟩
      intro u v
      exact (he u v).trans (hf (e u) (e v))

/-- The carrier of unlabelled n-vertex trees. -/
def UnlabelledTree (n : ℕ) := Quotient (treeSetoid n)

noncomputable def chosenTreeRep {n : ℕ} (T : UnlabelledTree n) : TreeRep n := Quotient.out T

/-- The disjoint-union graph with one new leaf attached at `v`. -/
def attachedBaseGraph {n : ℕ} (G : TreeRep n) (v : Fin n) :
    SimpleGraph (Fin n ⊕ Fin 1) :=
  (G.1 ⊕g (⊥ : SimpleGraph (Fin 1))) ⊔
    SimpleGraph.edge (Sum.inl v) (Sum.inr 0)

noncomputable def attachedGraph {n : ℕ} (G : TreeRep n) (v : Fin n) :
    SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.map (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (attachedBaseGraph G v)

lemma attachedBaseGraph_isTree {n : ℕ} (G : TreeRep n) (v : Fin n) :
    (attachedBaseGraph G v).IsTree := by
  classical
  let H : SimpleGraph (Fin n ⊕ Fin 1) := G.1 ⊕g (⊥ : SimpleGraph (Fin 1))
  let H' : SimpleGraph (Fin n ⊕ Fin 1) :=
    H ⊔ SimpleGraph.edge (Sum.inl v) (Sum.inr 0)
  have hsingleton : (⊥ : SimpleGraph (Fin 1)).IsTree :=
    SimpleGraph.IsTree.of_subsingleton
  have hconn : H'.Connected := by
    exact G.2.connected.sum_sup_edge hsingleton.connected
  have hsum_edges : H.edgeFinset.card = G.1.edgeFinset.card := by
    calc
      H.edgeFinset.card = Fintype.card H.edgeSet := H.edgeFinset_card
      _ = Fintype.card (G.1.edgeSet ⊕ (⊥ : SimpleGraph (Fin 1)).edgeSet) :=
        Fintype.card_congr SimpleGraph.edgeSetSumEquiv
      _ = Fintype.card G.1.edgeSet := by simp
      _ = G.1.edgeFinset.card := G.1.edgeFinset_card.symm
  have hnot : ¬ H.Adj (Sum.inl v) (Sum.inr 0) :=
    SimpleGraph.not_adj_sum_inl_inr _ _
  have hne : (Sum.inl v : Fin n ⊕ Fin 1) ≠ Sum.inr 0 := Sum.inl_ne_inr
  have hH_edges : H'.edgeFinset.card + 1 = n + 1 := by
    calc
      H'.edgeFinset.card + 1 = (H.edgeFinset.card + 1) + 1 := by
        exact congrArg (fun z => z + 1)
          (H.card_edgeFinset_sup_edge hnot hne)
      _ = (G.1.edgeFinset.card + 1) + 1 := by rw [hsum_edges]
      _ = n + 1 := by
        rw [G.2.card_edgeFinset]
        simp
  have htree : H'.IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    refine ⟨hconn, ?_⟩
    simpa [Nat.card_eq_fintype_card, H'.edgeFinset_card, Fintype.card_sum] using hH_edges
  simpa [attachedBaseGraph, H, H'] using htree

lemma attachedGraph_isTree {n : ℕ} (G : TreeRep n) (v : Fin n) :
    (attachedGraph G v).IsTree := by
  exact (SimpleGraph.Iso.map finSumFinEquiv (attachedBaseGraph G v)).isTree_iff.mp
    (attachedBaseGraph_isTree G v)


def isLeaf {n : ℕ} (G : TreeRep n) (v : Fin n) : Prop :=
  (G.1.neighborSet v).Nonempty ∧ (G.1.neighborSet v).Subsingleton

noncomputable def deleteTreeRep {n : ℕ} (G : TreeRep (n + 1))
    (v : Fin (n + 1)) (hv : isLeaf G v) : TreeRep n := by
  classical
  let s : Set (Fin (n + 1)) := {v}ᶜ
  have hs_card : Fintype.card {x // x ∈ s} = n := by
    have hc := Fintype.card_subtype_compl (α := Fin (n + 1)) (fun x => x = v)
    simpa [s] using hc
  let e : {x // x ∈ s} ≃ Fin n := Fintype.equivFinOfCardEq hs_card
  let H : SimpleGraph {x // x ∈ s} := G.1.induce s
  have hpre : H.Preconnected := by
    apply G.2.connected.preconnected.induce_of_degree_eq_one
    intro x hx
    have hxv : x = v := by simpa [s] using hx
    subst x
    exact hv.2
  have hnonempty : Nonempty {x // x ∈ s} := by
    rcases hv.1 with ⟨u, hu⟩
    refine ⟨⟨u, ?_⟩⟩
    simpa [s] using hu.ne.symm
  have hconn : H.Connected := by
    letI := hnonempty
    exact ⟨hpre⟩
  have htree : H.IsTree := by
    refine ⟨hconn, ?_⟩
    exact G.2.isAcyclic.induce s
  let K : SimpleGraph (Fin n) := SimpleGraph.map e H
  have hK : K.IsTree := by
    exact (SimpleGraph.Iso.map e H).isTree_iff.mp htree
  exact ⟨K, hK⟩

abbrev TreeVector (n : ℕ) := UnlabelledTree n →₀ ℚ

def LeafOccurrence {n : ℕ} (T : UnlabelledTree (n + 1)) :=
  {v : Fin (n + 1) // isLeaf (chosenTreeRep T) v}

noncomputable def deleteTree {n : ℕ} (T : UnlabelledTree (n + 1))
    (v : LeafOccurrence T) : UnlabelledTree n :=
  ⟦deleteTreeRep (chosenTreeRep T) v.1 v.2⟧

noncomputable def leafDeckBasis (n : ℕ) (T : UnlabelledTree (n + 1)) : TreeVector n := by
  classical
  letI : Finite (LeafOccurrence T) := by
    dsimp [LeafOccurrence]
    infer_instance
  letI := Fintype.ofFinite (LeafOccurrence T)
  exact ∑ v : LeafOccurrence T,
    (Finsupp.single (deleteTree T v) (1 : ℚ) : TreeVector n)

noncomputable def leafDeckSucc (n : ℕ) :
    TreeVector (n + 1) →ₗ[ℚ] TreeVector n :=
  Finsupp.lift (TreeVector n) ℚ (UnlabelledTree (n + 1)) (leafDeckBasis n)


noncomputable def leafDeckMap : (n : ℕ) → TreeVector n →ₗ[ℚ] TreeVector (n - 1)
  | 0 => 0
  | n + 1 => by simpa using (leafDeckSucc n)


def Motif := Σ n, UnlabelledTree n

noncomputable def motifCopies (H : Motif) (T : UnlabelledTree n) : ℕ := by
  classical
  letI := Fintype.ofFinite (chosenTreeRep T).1.Subgraph
  let I := {S : (chosenTreeRep T).1.Subgraph // Nonempty (S.coe ≃g (chosenTreeRep H.2).1)}
  exact Fintype.card I

noncomputable def motifEdges (H : Motif) : ℕ := by
  classical
  letI := Fintype.ofFinite (chosenTreeRep H.2).1.edgeSet
  exact Fintype.card (chosenTreeRep H.2).1.edgeSet

noncomputable def motifObservable (H : Motif) (n : ℕ) :
    TreeVector n →ₗ[ℚ] TreeVector n :=
  Finsupp.linearCombination ℚ (fun T =>
    (motifCopies H T : ℚ) • (Finsupp.single T (1 : ℚ) : TreeVector n))

def RetainedMotif (q : ℕ) :=
  {H : Motif // 1 ≤ motifEdges H ∧ motifEdges H ≤ q + 1}

def NonconstantMotif (q : ℕ) :=
  {H : Motif // 2 ≤ motifEdges H ∧ motifEdges H ≤ q + 1}

noncomputable def motifChannel (n q : ℕ) (H : RetainedMotif q) :
    TreeVector n →ₗ[ℚ] TreeVector (n - 1) :=
  (leafDeckMap n).comp (motifObservable H.1 n)

noncomputable def observabilityMap (n q : ℕ) :
    TreeVector n →ₗ[ℚ] (RetainedMotif q → TreeVector (n - 1)) :=
  { toFun := fun w H => motifChannel n q H w
    map_add' := by
      intro x y
      funext H
      simp [motifChannel]
    map_smul' := by
      intro a x
      funext H
      simp [motifChannel] }

noncomputable def motifObservabilityDefect (n q : ℕ) : Submodule ℚ (TreeVector n) :=
  LinearMap.ker (observabilityMap n q)

def defectVectorClaim5081 : Prop :=
  ∀ (n q : ℕ) (w : TreeVector n),
    w ∈ motifObservabilityDefect n q ↔
      w ∈ LinearMap.ker (leafDeckMap n) ∧
        ∀ H : NonconstantMotif q,
          motifObservable H.1 n w ∈ LinearMap.ker (leafDeckMap n)


abbrev RootedOccurrence (n : ℕ) := UnlabelledTree n × Fin n
abbrev RootedVector (n : ℕ) := RootedOccurrence n →₀ ℚ

noncomputable def attachOccurrence {n : ℕ} (x : RootedOccurrence n) : UnlabelledTree (n + 1) :=
  ⟦(⟨attachedGraph (chosenTreeRep x.1) x.2,
      attachedGraph_isTree (chosenTreeRep x.1) x.2⟩ : TreeRep (n + 1))⟧

noncomputable def rootedBasis {n : ℕ} (x : RootedOccurrence n) : RootedVector n :=
  Finsupp.single x (1 : ℚ)

noncomputable def attachmentMap (n : ℕ) :
    RootedVector n →ₗ[ℚ] TreeVector (n + 1) :=
  Finsupp.linearCombination ℚ (fun x =>
    (Finsupp.single (attachOccurrence x) (1 : ℚ) : TreeVector (n + 1)))

noncomputable def globalLeafExchangeSyzygySpace (n : ℕ) :
    Submodule ℚ (RootedVector n) :=
  LinearMap.ker (attachmentMap n)

def leafExchangeGenerators (n : ℕ) : Set (RootedVector n) :=
  {z | ∃ x y : RootedOccurrence n,
    attachOccurrence x = attachOccurrence y ∧
      z = rootedBasis x - rootedBasis y}

noncomputable def globalLeafExchangeClaim5135 : Prop :=
  ∀ n : ℕ,
    globalLeafExchangeSyzygySpace n =
      Submodule.span ℚ (leafExchangeGenerators n)

end MathlibPlus.Open.Combinatorics
