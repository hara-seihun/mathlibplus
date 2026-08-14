import Mathlib

namespace ProjectsResearch.TreeDeck

abbrev LabelledTree (n : ℕ) := {G : SimpleGraph (Fin n) // G.IsTree}

def Relabelled {n : ℕ} (G H : LabelledTree n) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ u v, G.1.Adj u v ↔ H.1.Adj (e u) (e v)

lemma relabelled_refl {n : ℕ} (G : LabelledTree n) : Relabelled G G := by
  exact ⟨Equiv.refl _, fun u v => Iff.rfl⟩

lemma relabelled_symm {n : ℕ} {G H : LabelledTree n} :
    Relabelled G H → Relabelled H G := by
  rintro ⟨e, h⟩
  refine ⟨e.symm, ?_⟩
  intro u v
  simpa using (h (e.symm u) (e.symm v)).symm

lemma relabelled_trans {n : ℕ} {G H K : LabelledTree n} :
    Relabelled G H → Relabelled H K → Relabelled G K := by
  rintro ⟨e, h⟩ ⟨f, h'⟩
  refine ⟨e.trans f, ?_⟩
  intro u v
  exact (h u v).trans (h' (e u) (e v))

instance treeSetoid (n : ℕ) : Setoid (LabelledTree n) where
  r := Relabelled
  iseqv := ⟨relabelled_refl, relabelled_symm, relabelled_trans⟩

def UnlabelledTree (n : ℕ) := Quotient (treeSetoid n)

abbrev TreeState (n : ℕ) := UnlabelledTree n →₀ ℚ

noncomputable instance graphNeighborFintype {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    Fintype (G.neighborSet v) := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter (fun w : Fin n => w ∈ G.neighborSet v)) (by simp)

noncomputable instance graphEdgeFintype {n : ℕ} (G : SimpleGraph (Fin n)) :
    Fintype G.edgeSet := by
  classical
  exact Fintype.ofFinset
    (Finset.univ.filter (fun e : Sym2 (Fin n) => e ∈ G.edgeSet)) (by simp)

noncomputable def relabelIso {n : ℕ} {G H : LabelledTree n} (h : Relabelled G H) :
    G.1 ≃g H.1 := by
  let e := Classical.choose h
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro a b
  exact (Classical.choose_spec h a b).symm

lemma edgeFinset_card_relabelled {n : ℕ} {G H : LabelledTree n} (h : Relabelled G H) :
    G.1.edgeFinset.card = H.1.edgeFinset.card := by
  rw [SimpleGraph.edgeFinset, SimpleGraph.edgeFinset]
  rw [Set.toFinset_card, Set.toFinset_card]
  exact Fintype.card_congr (relabelIso h).mapEdgeSet

lemma edgeSet_top_fin_two :
    (⊤ : SimpleGraph (Fin 2)).edgeSet = {Sym2.mk (0 : Fin 2) 1} := by
  ext e
  refine Sym2.inductionOn e ?_
  intro a b
  fin_cases a <;> fin_cases b <;> simp [SimpleGraph.mem_edgeSet]

lemma edgeFinset_card_top_fin_two :
    (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1 := by
  change ((⊤ : SimpleGraph (Fin 2)).edgeSet.toFinset).card = 1
  calc
    ((⊤ : SimpleGraph (Fin 2)).edgeSet.toFinset).card =
        Fintype.card (⊤ : SimpleGraph (Fin 2)).edgeSet :=
      Set.toFinset_card _
    _ = Fintype.card ({Sym2.mk (0 : Fin 2) 1} : Set (Sym2 (Fin 2))) :=
      Fintype.card_congr (Equiv.setCongr edgeSet_top_fin_two)
    _ = 1 := by
      have h : Fintype.card ({Sym2.mk (0 : Fin 2) 1} : Set (Sym2 (Fin 2))) =
          ({Sym2.mk (0 : Fin 2) 1} : Finset (Sym2 (Fin 2))).card :=
        Fintype.card_ofFinset ({Sym2.mk (0 : Fin 2) 1} : Finset (Sym2 (Fin 2))) (by simp)
      simpa using h

noncomputable def deletedVertexSet {n : ℕ} (v : Fin n) : Set (Fin n) :=
  (↑(Finset.univ.erase v) : Set (Fin n))

noncomputable def deletionEquiv {n : ℕ} (v : Fin n) :
    Fin (n - 1) ≃ deletedVertexSet v :=
  (Finset.orderIsoOfFin (Finset.univ.erase v) (by simp)).toEquiv

noncomputable def deleteGraph {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    SimpleGraph (Fin (n - 1)) :=
  SimpleGraph.comap (deletionEquiv v) (G.induce (deletedVertexSet v))

lemma deleteGraph_isTree {n : ℕ} (G : LabelledTree n) (v : Fin n)
    (hv : G.1.degree v = 1) : (deleteGraph G.1 v).IsTree := by
  have hset : deletedVertexSet v = ({v}ᶜ : Set (Fin n)) := by
    ext w
    simp [deletedVertexSet]
  have hconn : (G.1.induce (deletedVertexSet v)).Connected := by
    rw [hset]
    exact G.2.connected.induce_compl_singleton_of_degree_eq_one hv
  have hacyc : (G.1.induce (deletedVertexSet v)).IsAcyclic :=
    G.2.isAcyclic.induce _
  have htree : (G.1.induce (deletedVertexSet v)).IsTree := ⟨hconn, hacyc⟩
  exact (SimpleGraph.Iso.comap (deletionEquiv v) (G.1.induce (deletedVertexSet v))).isTree_iff.mpr htree

noncomputable def leafVertices (T : UnlabelledTree n) : Type :=
  {v : Fin n // (Quotient.out T).1.degree v = 1}

noncomputable instance leafVerticesFintype {n : ℕ} (T : UnlabelledTree n) :
    Fintype (leafVertices T) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun v : Fin n => (Quotient.out T).1.degree v = 1)) (by simp)

noncomputable def leafCard {n : ℕ} (T : UnlabelledTree n) (v : leafVertices T) :
    UnlabelledTree (n - 1) :=
  Quotient.mk (treeSetoid (n - 1))
    ⟨deleteGraph (Quotient.out T).1 v.1,
      deleteGraph_isTree (Quotient.out T) v.1 v.2⟩

noncomputable def leafDeckOnBasis {n : ℕ} (T : UnlabelledTree n) : TreeState (n - 1) :=
  ∑ v : leafVertices T, Finsupp.single (leafCard T v) (1 : ℚ)

noncomputable def leafDeck (n : ℕ) : TreeState n →ₗ[ℚ] TreeState (n - 1) :=
  Finsupp.linearCombination ℚ (leafDeckOnBasis (n := n))

def IsOrdinaryCopy {m n : ℕ} (H : LabelledTree m) (T : LabelledTree n)
    (f : Fin m → Fin n) : Prop :=
  Function.Injective f ∧ ∀ ⦃u w⦄, H.1.Adj u w → T.1.Adj (f u) (f w)

noncomputable def ordinaryCopyImages {m n : ℕ} (H : LabelledTree m) (T : LabelledTree n) :
    Finset (Set (Sym2 (Fin n))) := by
  classical
  exact (Finset.univ.filter (fun f : Fin m → Fin n => IsOrdinaryCopy H T f)).image
    (fun f => Sym2.map f '' H.1.edgeSet)

noncomputable def motifCopyCount {m n : ℕ} (H : UnlabelledTree m) (T : UnlabelledTree n) : ℕ :=
  (ordinaryCopyImages (Quotient.out H) (Quotient.out T)).card

noncomputable def motifEdgeCount {m : ℕ} : UnlabelledTree m → ℕ :=
  Quotient.lift (fun H : LabelledTree m => H.1.edgeFinset.card)
    (fun G H h => edgeFinset_card_relabelled h)

abbrev TreeMotif := Σ m : ℕ, UnlabelledTree m

def MotifIndex (q : ℕ) :=
  {H : TreeMotif // 1 ≤ motifEdgeCount H.2 ∧ motifEdgeCount H.2 ≤ q + 1}

noncomputable def motifDiagonal {m : ℕ} (H : UnlabelledTree m) (n : ℕ) :
    TreeState n →ₗ[ℚ] TreeState n :=
  Finsupp.linearCombination ℚ (fun T =>
    (motifCopyCount H T : ℚ) • Finsupp.single T (1 : ℚ))

noncomputable def observabilityMap (n q : ℕ) :
    TreeState n →ₗ[ℚ] (MotifIndex q → TreeState (n - 1)) :=
  LinearMap.pi (fun i => (leafDeck n).comp (motifDiagonal i.1.2 n))

noncomputable def kTwoTree : UnlabelledTree 2 :=
  Quotient.mk (treeSetoid 2)
    ⟨(⊤ : SimpleGraph (Fin 2)), by
      exact ⟨SimpleGraph.connected_top,
        SimpleGraph.IsAcyclic.of_card_le_two (by simp)⟩⟩

lemma kTwoTree_edgeCount : motifEdgeCount kTwoTree = 1 := by
  simpa [motifEdgeCount, kTwoTree] using edgeFinset_card_top_fin_two

noncomputable def kTwoIndex (q : ℕ) : MotifIndex q := by
  refine ⟨⟨2, kTwoTree⟩, ?_⟩
  change 1 ≤ motifEdgeCount kTwoTree ∧ motifEdgeCount kTwoTree ≤ q + 1
  rw [kTwoTree_edgeCount]
  omega

end ProjectsResearch.TreeDeck

namespace MathlibPlus.Open.Combinatorics

open ProjectsResearch.TreeDeck

def kTwoChannelContainsLeafDeck : Prop :=
  (∀ n : ℕ, ∀ T : UnlabelledTree n,
      motifCopyCount kTwoTree T = n - 1) ∧
  (∀ n : ℕ,
      (leafDeck n).comp (motifDiagonal kTwoTree n) =
        ((n - 1 : ℕ) : ℚ) • leafDeck n) ∧
  (∀ n q : ℕ, 2 ≤ n →
      (LinearMap.proj (kTwoIndex q)).comp (observabilityMap n q) =
          ((n - 1 : ℕ) : ℚ) • leafDeck n ∧
        ((n - 1 : ℕ) : ℚ) ≠ 0)

end MathlibPlus.Open.Combinatorics
