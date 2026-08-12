import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace MathlibPlus.GraphTheory.Claim25657

open scoped BigOperators

/-
The source calls the three cardinalities below a pair profile.  We make the
cell convention explicit: the second and third cells delete the other endpoint
when the pair is adjacent.  This is the usual ordered-pair profile of an SRG.
-/

theorem pairCellProfile_of_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n k ell mu : ℕ} (h : G.IsSRGWith n k ell mu)
    {v w : V} (ha : G.Adj v w) :
    ((G.commonNeighbors v w).ncard,
      (G.neighborSet v \ (G.neighborSet w ∪ {w})).ncard,
      (G.neighborSet w \ (G.neighborSet v ∪ {v})).ncard) =
      (ell, k - 1 - ell, k - 1 - ell) := by
  have hcommon : (G.commonNeighbors v w).ncard = ell := by
    simpa only [Set.fintypeCard_eq_ncard] using h.of_adj v w ha
  have hnv : (G.neighborSet v).ncard = k := by
    calc
      (G.neighborSet v).ncard = Fintype.card (G.neighborSet v) := by
        simpa using (Set.fintypeCard_eq_ncard (s := G.neighborSet v)).symm
      _ = G.degree v := G.card_neighborSet_eq_degree v
      _ = k := h.regular.degree_eq v
  have hnw : (G.neighborSet w).ncard = k := by
    calc
      (G.neighborSet w).ncard = Fintype.card (G.neighborSet w) := by
        simpa using (Set.fintypeCard_eq_ncard (s := G.neighborSet w)).symm
      _ = G.degree w := G.card_neighborSet_eq_degree w
      _ = k := h.regular.degree_eq w
  have hcellv :
      (G.neighborSet v ∩ (G.neighborSet w ∪ {w})).ncard = ell + 1 := by
    have hset : G.neighborSet v ∩ (G.neighborSet w ∪ {w}) =
        G.commonNeighbors v w ∪ {w} := by
      ext x
      by_cases hx : x = w
      · subst x
        simp [ha]
      · simp [SimpleGraph.commonNeighbors, hx]
    rw [hset, Set.union_singleton]
    rw [Set.ncard_insert_of_notMem (G.notMem_commonNeighbors_right v w)]
    simp [hcommon]
  have hcellw :
      (G.neighborSet w ∩ (G.neighborSet v ∪ {v})).ncard = ell + 1 := by
    have hset : G.neighborSet w ∩ (G.neighborSet v ∪ {v}) =
        G.commonNeighbors w v ∪ {v} := by
      ext x
      by_cases hx : x = v
      · subst x
        have haw : G.Adj w v := (G.adj_comm v w).mp ha
        simp [haw]
      · simp [SimpleGraph.commonNeighbors, hx]
    rw [hset, Set.union_singleton]
    rw [Set.ncard_insert_of_notMem (G.notMem_commonNeighbors_right w v)]
    simpa [hcommon, G.commonNeighbors_symm]
  have hdiffv := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet v) (G.neighborSet w ∪ {w})
  have hdiffw := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet w) (G.neighborSet v ∪ {v})
  have hdiffv' :
      (G.neighborSet v \ (G.neighborSet w ∪ {w})).ncard = k - (ell + 1) := by
    omega
  have hdiffw' :
      (G.neighborSet w \ (G.neighborSet v ∪ {v})).ncard = k - (ell + 1) := by
    have hdiffw2 : (ell + 1) +
        (G.neighborSet w \ (G.neighborSet v ∪ {v})).ncard = k := by
      simpa only [hcellw, hnw] using hdiffw
    omega
  rw [hcommon, hdiffv', hdiffw']
  have hsub : k - (ell + 1) = k - 1 - ell := by
    omega
  rw [hsub]

theorem pairCellProfile_of_not_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n k ell mu : ℕ} (h : G.IsSRGWith n k ell mu)
    {v w : V} (hne : v ≠ w) (hna : ¬G.Adj v w) :
    ((G.commonNeighbors v w).ncard,
      (G.neighborSet v \ (G.neighborSet w ∪ {w})).ncard,
      (G.neighborSet w \ (G.neighborSet v ∪ {v})).ncard) =
      (mu, k - mu, k - mu) := by
  have hcommon : (G.commonNeighbors v w).ncard = mu := by
    simpa only [Set.fintypeCard_eq_ncard] using h.of_not_adj hne hna
  have hnv : (G.neighborSet v).ncard = k := by
    calc
      (G.neighborSet v).ncard = Fintype.card (G.neighborSet v) := by
        simpa using (Set.fintypeCard_eq_ncard (s := G.neighborSet v)).symm
      _ = G.degree v := G.card_neighborSet_eq_degree v
      _ = k := h.regular.degree_eq v
  have hnw : (G.neighborSet w).ncard = k := by
    calc
      (G.neighborSet w).ncard = Fintype.card (G.neighborSet w) := by
        simpa using (Set.fintypeCard_eq_ncard (s := G.neighborSet w)).symm
      _ = G.degree w := G.card_neighborSet_eq_degree w
      _ = k := h.regular.degree_eq w
  have hsetv : G.neighborSet v ∩ (G.neighborSet w ∪ {w}) =
      G.commonNeighbors v w := by
    ext x
    by_cases hx : x = w
    · subst x
      simp [SimpleGraph.commonNeighbors, hna]
    · simp [SimpleGraph.commonNeighbors, hx]
  have hwan : ¬ G.Adj w v := by
    intro hw
    exact hna ((G.adj_comm w v).mp hw)
  have hsetw : G.neighborSet w ∩ (G.neighborSet v ∪ {v}) =
      G.commonNeighbors w v := by
    ext x
    by_cases hx : x = v
    · subst x
      simp [SimpleGraph.commonNeighbors, hwan]
    · simp [SimpleGraph.commonNeighbors, hx]
  have hcellv :
      (G.neighborSet v ∩ (G.neighborSet w ∪ {w})).ncard = mu := by
    rw [hsetv, hcommon]
  have hcellw :
      (G.neighborSet w ∩ (G.neighborSet v ∪ {v})).ncard = mu := by
    rw [hsetw, G.commonNeighbors_symm, hcommon]
  have hdiffv := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet v) (G.neighborSet w ∪ {w})
  have hdiffw := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (G.neighborSet w) (G.neighborSet v ∪ {v})
  have hdiffv' :
      (G.neighborSet v \ (G.neighborSet w ∪ {w})).ncard = k - mu := by
    omega
  have hdiffw' :
      (G.neighborSet w \ (G.neighborSet v ∪ {v})).ncard = k - mu := by
    omega
  rw [hcommon, hdiffv', hdiffw']

end MathlibPlus.GraphTheory.Claim25657
