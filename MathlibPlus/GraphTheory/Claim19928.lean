import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.GraphTheory

/-- The degree of a vertex is the number of edges removed by deleting it. -/
theorem degree_eq_edgeCount_sub_deletedVertex_claim19928
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v = G.edgeFinset.card - (G.induce {v}ᶜ).edgeFinset.card := by
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have hdeg : G.degree v ≤ G.edgeFinset.card :=
    SimpleGraph.degree_le_card_edgeFinset G v
  omega

/-- Summing the edge counts of all vertex-deleted cards. -/
theorem sum_deletedVertex_edgeCounts_claim19928
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
      (Fintype.card V - 2) * G.edgeFinset.card := by
  simp_rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  change (Finset.univ.sum (fun v : V => G.edgeFinset.card - G.degree v)) = _
  rw [Finset.sum_tsub_distrib Finset.univ (fun v _ ↦
    SimpleGraph.degree_le_card_edgeFinset G v)]
  rw [Finset.sum_const, SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [Finset.card_univ, nsmul_eq_mul]
  rw [Nat.sub_mul]
  simp

/-- For at least three vertices, the edge count is recovered by division. -/
theorem edgeCount_eq_sum_deletedVertex_edgeCounts_div_claim19928
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : 3 ≤ Fintype.card V) :
    G.edgeFinset.card =
      (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) /
        (Fintype.card V - 2) := by
  have hs : (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
      (Fintype.card V - 2) * G.edgeFinset.card := by
    simp_rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
      SimpleGraph.card_edgeFinset_deleteIncidenceSet]
    change (Finset.univ.sum (fun v : V => G.edgeFinset.card - G.degree v)) = _
    rw [Finset.sum_tsub_distrib Finset.univ (fun v _ ↦
      SimpleGraph.degree_le_card_edgeFinset G v)]
    rw [Finset.sum_const, SimpleGraph.sum_degrees_eq_twice_card_edges]
    simp only [Finset.card_univ, nsmul_eq_mul]
    rw [Nat.sub_mul]
    simp
  rw [hs]
  exact (Nat.mul_div_cancel_left _ (by omega)).symm

end MathlibPlus.GraphTheory
