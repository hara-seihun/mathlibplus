import MathlibPlus.GraphTheory.Claim19928

open scoped BigOperators

namespace MathlibPlus.GraphTheory.Claim20718

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
  exact ⟨MathlibPlus.GraphTheory.sum_deletedVertex_edgeCounts_claim19928 G,
    MathlibPlus.GraphTheory.edgeCount_eq_sum_deletedVertex_edgeCounts_div_claim19928 G⟩

end MathlibPlus.GraphTheory.Claim20718
