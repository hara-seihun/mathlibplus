import MathlibPlus.Ramsey55

namespace MathlibPlus.GraphTheory

/-- In a `(5,5)`-good graph, the induced graph on the common neighbors of
adjacent vertices has neither a triangle nor an independent five-set. -/
theorem commonNeighborInduced_isGood_claim21824
    {V : Type*} (G : SimpleGraph V)
    (hgood : G.CliqueFree 5 ∧ G.IndepSetFree 5)
    (u v : V) (huv : G.Adj u v) :
    (G.induce (G.commonNeighbors u v)).CliqueFree 3 ∧
      (G.induce (G.commonNeighbors u v)).IndepSetFree 5 := by
  classical
  have clique_insert : ∀ (w : V) (s : Finset V),
      G.IsClique (↑s) → w ∉ s → (∀ x ∈ s, G.Adj w x) →
      G.IsClique (↑(insert w s)) := by
    intro w s hs hws hadj
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact False.elim (hxy rfl)
      · exact hadj y hy
    · rcases hy with rfl | hy
      · simpa [SimpleGraph.adj_comm] using hadj x hx
      · exact hs hx hy hxy
  constructor
  · intro s hs
    have hcardS : s.card = 3 := hs.card_eq
    let emb : {x // x ∈ G.commonNeighbors u v} ↪ V :=
      Function.Embedding.subtype _
    let aSet : Finset V := s.map emb
    have hcardA : aSet.card = 3 := by
      dsimp [aSet]
      rw [Finset.card_map]
      exact hcardS
    have hA_common : ∀ x ∈ aSet, x ∈ G.commonNeighbors u v := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      exact x'.property
    have hclA : G.IsClique (↑aSet) := by
      rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro h
        apply hxy
        simpa [h]
      have hind : (G.induce (G.commonNeighbors u v)).Adj x' y' :=
        hs.isClique (by simpa using hx') (by simpa using hy') hxy'
      exact SimpleGraph.induce_adj.mp hind
    have huA : u ∉ aSet := by
      intro huA
      have hcu := (G.mem_commonNeighbors).mp (hA_common u huA)
      exact hcu.1.ne rfl
    have hvA : v ∉ aSet := by
      intro hvA
      have hcv := (G.mem_commonNeighbors).mp (hA_common v hvA)
      exact hcv.2.ne rfl
    have hclV : G.IsClique (↑(insert v aSet)) := by
      apply clique_insert v aSet hclA hvA
      intro x hx
      exact ((G.mem_commonNeighbors).mp (hA_common x hx)).2
    have huV : u ∉ insert v aSet := by
      intro h
      simp only [Finset.mem_insert] at h
      rcases h with h | h
      · exact huv.ne h
      · exact huA h
    have hclAll : G.IsClique (↑(insert u (insert v aSet))) := by
      apply clique_insert u (insert v aSet) hclV huV
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact huv
      · exact ((G.mem_commonNeighbors).mp (hA_common x hx)).1
    have hcardAll : (insert u (insert v aSet)).card = 5 := by
      simp [hcardA, huA, hvA, huv.ne]
    exact (hgood.1 (insert u (insert v aSet)))
      ⟨hclAll, hcardAll⟩
  · intro s hs
    have hcardS : s.card = 5 := hs.card_eq
    let emb : {x // x ∈ G.commonNeighbors u v} ↪ V :=
      Function.Embedding.subtype _
    let aSet : Finset V := s.map emb
    have hcardA : aSet.card = 5 := by
      dsimp [aSet]
      rw [Finset.card_map]
      exact hcardS
    have hindA : G.IsIndepSet (↑aSet) := by
      rw [SimpleGraph.isIndepSet_iff]
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro h
        apply hxy
        simpa [h]
      have hind := hs.isIndepSet (by simpa using hx') (by simpa using hy') hxy'
      intro hadj
      exact hind (SimpleGraph.induce_adj.mpr hadj)
    exact (hgood.2 aSet) ⟨hindA, hcardA⟩

end MathlibPlus.GraphTheory
