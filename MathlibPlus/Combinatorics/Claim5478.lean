import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MathlibPlus.Combinatorics

open scoped BigOperators

/--
For a finite reduced subcubic tree (so every vertex has degree one or three),
there are two more pendant vertices than trivalent vertices.  If the
trivalent vertices are nonempty, the tree induced by them has one fewer edge
than vertices.

The source's phrase “ordered” carries no extra graph-theoretic condition in
this count, so no arbitrary order is introduced here.  Pendant slots are
represented by degree-one vertices, and internal edges by the edge set of the
induced graph on degree-three vertices.
-/
theorem reducedSubcubicTree_slots_internalEdges_claim5478
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTree : G.IsTree)
    (hdeg : ∀ v : V, G.degree v = 1 ∨ G.degree v = 3)
    (hbranch_nonempty :
      (Finset.univ.filter (fun v => G.degree v = 3)).Nonempty) :
    let leaves : Finset V := Finset.univ.filter (fun v => G.degree v = 1)
    let branch : Finset V := Finset.univ.filter (fun v => G.degree v = 3)
    leaves.card = branch.card + 2 ∧
      {e ∈ G.edgeFinset | e.toFinset ⊆ branch}.card = branch.card - 1 := by
  classical
  let leaves : Finset V := Finset.univ.filter (fun v => G.degree v = 1)
  let branch : Finset V := Finset.univ.filter (fun v => G.degree v = 3)
  have hdis : Disjoint leaves branch := by
    rw [Finset.disjoint_left]
    intro v hvL hvB
    simp only [leaves, branch, Finset.mem_filter, Finset.mem_univ, true_and] at hvL hvB
    omega
  have hunion : leaves ∪ branch = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    rcases hdeg v with h | h
    · exact Finset.mem_union_left _ (by simp [leaves, h])
    · exact Finset.mem_union_right _ (by simp [branch, h])
  have hcardV : Fintype.card V = leaves.card + branch.card := by
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdis]
  have hsumL : (∑ v ∈ leaves, G.degree v) = leaves.card := by
    calc
      (∑ v ∈ leaves, G.degree v) = (∑ v' ∈ leaves, (1 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hv
      _ = leaves.card := by simp
  have hsumB : (∑ v ∈ branch, G.degree v) = 3 * branch.card := by
    calc
      (∑ v ∈ branch, G.degree v) = (∑ v' ∈ branch, (3 : ℕ)) := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [branch, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hv
      _ = 3 * branch.card := by simp [Nat.mul_comm]
  have hsum : ∑ v : V, G.degree v = leaves.card + 3 * branch.card := by
    rw [← hunion, Finset.sum_union hdis, hsumL, hsumB]
  have hE : G.edgeFinset.card + 1 = Fintype.card V := by
    exact hTree.card_edgeFinset
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hpc : (G.induce (branch : Set V)).Preconnected := by
    apply hTree.connected.preconnected.induce_of_degree_eq_one
    intro v hv
    have hv3 : G.degree v ≠ 3 := by
      intro hv3
      apply hv
      simp [branch, hv3]
    have hv1 : G.degree v = 1 := by
      rcases hdeg v with hv1 | hv3'
      · exact hv1
      · exact False.elim (hv3 hv3')
    have hcard : Fintype.card (G.neighborSet v) ≤ 1 := by
      rw [G.card_neighborSet_eq_degree]
      omega
    exact (Set.subsingleton_coe _).mp (Fintype.card_le_one_iff_subsingleton.mp hcard)
  have hbranch_tree : (G.induce (branch : Set V)).IsTree := by
    obtain ⟨v, hv⟩ := hbranch_nonempty
    letI : Nonempty (branch : Set V) := ⟨⟨v, by simpa [branch] using hv⟩⟩
    exact ⟨⟨hpc⟩, hTree.isAcyclic.induce (branch : Set V)⟩
  have hinternal : {e ∈ G.edgeFinset | e.toFinset ⊆ branch}.card = branch.card - 1 := by
    rw [SimpleGraph.card_filter_edgeFinset_toFinset_subset]
    have hcard := hbranch_tree.card_edgeFinset
    have hcard' : (G.induce (branch : Set V)).edgeFinset.card + 1 = branch.card := by
      simpa using hcard
    omega
  change leaves.card = branch.card + 2 ∧
    {e ∈ G.edgeFinset | e.toFinset ⊆ branch}.card = branch.card - 1
  constructor
  · omega
  · exact hinternal

end MathlibPlus.Combinatorics
