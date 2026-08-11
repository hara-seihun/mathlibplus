import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open scoped BigOperators

namespace MathlibPlus.GraphTheory.Claim20718

/-- For a vertex-deleted card, the deleted vertex degree is the host edge count
minus the card edge count. -/
theorem deletedVertexDegreeFromCard
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    G.degree v = G.edgeFinset.card - (G.induce {v}ᶜ).edgeFinset.card := by
  classical
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  exact (Nat.sub_sub_self (G.degree_le_card_edgeFinset v)).symm

/-- The vertex-deck edge-count identity and the resulting reconstruction quotient. -/
theorem vertexDeckEdgeCountAndReconstruction
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
        (Fintype.card V - 2) * G.edgeFinset.card ∧
      (3 ≤ Fintype.card V →
        G.edgeFinset.card =
          (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) /
            (Fintype.card V - 2)) := by
  let m : ℕ := G.edgeFinset.card
  have hdelete (v : V) :
      (G.induce {v}ᶜ).edgeFinset.card = m - G.degree v := by
    dsimp [m]
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
      SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have hsumdeg : (∑ v : V, G.degree v) = 2 * m := by
    simpa [m] using G.sum_degrees_eq_twice_card_edges
  have hsumadd :
      (∑ v : V, (m - G.degree v)) + ∑ v : V, G.degree v =
        ∑ v : V, m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    exact Nat.sub_add_cancel (G.degree_le_card_edgeFinset v)
  have hsumcore :
      (∑ v : V, (m - G.degree v)) + 2 * m = Fintype.card V * m := by
    calc
      (∑ v : V, (m - G.degree v)) + 2 * m =
          (∑ v : V, (m - G.degree v)) + ∑ v : V, G.degree v := by
            rw [hsumdeg]
      _ = ∑ v : V, m := hsumadd
      _ = Fintype.card V * m := by simp
  have hsumcards :
      (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
        ∑ v : V, (m - G.degree v) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact hdelete v
  have hsum :
      (∑ v : V, (G.induce {v}ᶜ).edgeFinset.card) =
        (Fintype.card V - 2) * m := by
    rw [hsumcards, Nat.sub_mul]
    have hle : 2 * m ≤ Fintype.card V * m := by
      rw [← hsumcore]
      exact Nat.le_add_left _ _
    exact ((Nat.sub_eq_iff_eq_add hle).2 hsumcore.symm).symm
  constructor
  · simpa [m] using hsum
  · intro hcard
    rw [hsum, Nat.mul_div_cancel_left]
    exact Nat.sub_pos_of_lt (by omega)

end MathlibPlus.GraphTheory.Claim20718
