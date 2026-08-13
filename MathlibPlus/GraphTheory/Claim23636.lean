import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace MathlibPlus.GraphTheory.Claim23636

/-- A finite connected graph with at least two vertices has two distinct
vertices whose deletion leaves a connected induced card. -/
theorem two_connected_deletion_cards
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (hcard : 2 ≤ Fintype.card V) :
    ∃ u v : V, u ≠ v ∧
      (G.induce {u}ᶜ).Connected ∧ (G.induce {v}ᶜ).Connected := by
  classical
  letI : Nontrivial V :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨T, hTle, hTtree⟩ := hG.exists_isTree_le
  obtain ⟨u, v, huv, hu, hv⟩ := hTtree.exists_ne_and_degree_eq_one
  refine ⟨u, v, huv, ?_, ?_⟩
  · exact (hTtree.connected.induce_compl_singleton_of_degree_eq_one hu).mono
      (by
        intro x y hxy
        exact hTle hxy)
  · exact (hTtree.connected.induce_compl_singleton_of_degree_eq_one hv).mono
      (by
        intro x y hxy
        exact hTle hxy)

end MathlibPlus.GraphTheory.Claim23636
