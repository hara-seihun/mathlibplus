import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.GraphTheory

/-- Claim 20472: exact ordered-pair profiles and multiplicities in a strongly regular graph.

For adjacent pairs the exclusive-neighbour sets omit the two endpoints, matching the
source's `k - 1 - λ` profile entries.  Nonadjacent pairs are distinct ordered pairs,
so their exclusive sets need no endpoint deletion. -/
theorem stronglyRegularPairProfile_claim20472
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k l μ : ℕ} (h : G.IsSRGWith n k l μ) :
    (∀ v w, G.Adj v w →
      ((G.neighborFinset v ∩ G.neighborFinset w).card,
        (G.neighborFinset v \ (G.neighborFinset w ∪ {w})).card,
        (G.neighborFinset w \ (G.neighborFinset v ∪ {v})).card)
        = (l, k - 1 - l, k - 1 - l)) ∧
    (∀ v w, v ≠ w → ¬ G.Adj v w →
      ((G.neighborFinset v ∩ G.neighborFinset w).card,
        (G.neighborFinset v \ G.neighborFinset w).card,
        (G.neighborFinset w \ G.neighborFinset v).card)
        = (μ, k - μ, k - μ)) ∧
    (∑ v : V, Fintype.card {w : V // G.Adj v w}) = n * k ∧
    (∑ v : V, Fintype.card {w : V // v ≠ w ∧ ¬ G.Adj v w}) = n * (n - 1 - k) := by
  classical
  have hcommon : ∀ v w,
      (G.neighborFinset v ∩ G.neighborFinset w).card =
        Fintype.card (G.commonNeighbors v w) := by
    intro v w
    calc
      (G.neighborFinset v ∩ G.neighborFinset w).card =
          (G.commonNeighbors v w).toFinset.card := by
        apply congrArg Finset.card
        ext x
        constructor
        · intro hx
          have hv : G.Adj v x :=
            (G.mem_neighborFinset v x).1 (Finset.mem_inter.mp hx).1
          have hw : G.Adj w x :=
            (G.mem_neighborFinset w x).1 (Finset.mem_inter.mp hx).2
          have hxcommon : x ∈ G.commonNeighbors v w :=
            (G.mem_commonNeighbors).2 ⟨hv, hw⟩
          rw [← (G.commonNeighbors v w).toFinite.toFinset_eq_toFinset]
          exact (G.commonNeighbors v w).toFinite.mem_toFinset.2 hxcommon
        · intro hx
          rw [← (G.commonNeighbors v w).toFinite.toFinset_eq_toFinset] at hx
          have hxcommon : x ∈ G.commonNeighbors v w :=
            (G.commonNeighbors v w).toFinite.mem_toFinset.1 hx
          have hvw : G.Adj v x ∧ G.Adj w x :=
            (G.mem_commonNeighbors).1 hxcommon
          exact Finset.mem_inter.mpr ⟨
            (G.mem_neighborFinset v x).2 hvw.1,
            (G.mem_neighborFinset w x).2 hvw.2⟩
      _ = Fintype.card (G.commonNeighbors v w) := Set.toFinset_card _
  have hdeg : ∀ v, (G.neighborFinset v).card = k := by
    intro v
    rw [G.card_neighborFinset_eq_degree, h.regular.degree_eq]
  have hadj_left : ∀ v w, G.Adj v w →
      (G.neighborFinset v \ (G.neighborFinset w ∪ {w})).card = k - 1 - l := by
    intro v w hvw
    have hwv : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).2 hvw
    have hww : w ∉ G.neighborFinset w := G.notMem_neighborFinset_self w
    have hinter : G.neighborFinset v ∩ (G.neighborFinset w ∪ {w}) =
        (G.neighborFinset v ∩ G.neighborFinset w) ∪ {w} := by
      rw [Finset.inter_union_distrib_left]
      have hsingle : G.neighborFinset v ∩ {w} = ({w} : Finset V) := by
        simp [hwv]
      rw [hsingle]
    have hdisj : Disjoint (G.neighborFinset v ∩ G.neighborFinset w) ({w} : Finset V) := by
      rw [Finset.disjoint_singleton_right]
      intro hwcommon
      exact hww (Finset.mem_inter.mp hwcommon).2
    have hcardinter : (G.neighborFinset v ∩
        (G.neighborFinset w ∪ {w})).card =
        (G.neighborFinset v ∩ G.neighborFinset w).card + 1 := by
      rw [hinter, Finset.card_union_of_disjoint hdisj]
      simp
    have hsplit := Finset.card_sdiff_add_card_inter
      (G.neighborFinset v) (G.neighborFinset w ∪ {w})
    have hcl : (G.neighborFinset v ∩ G.neighborFinset w).card = l := by
      rw [hcommon, h.of_adj v w hvw]
    rw [hcardinter, hdeg v, hcl] at hsplit
    omega
  have hnotadj_left : ∀ v w, v ≠ w → ¬ G.Adj v w →
      (G.neighborFinset v \ G.neighborFinset w).card = k - μ := by
    intro v w hne hn
    have hsplit := Finset.card_sdiff_add_card_inter
      (G.neighborFinset v) (G.neighborFinset w)
    have hcl : (G.neighborFinset v ∩ G.neighborFinset w).card = μ := by
      rw [hcommon, h.of_not_adj hne hn]
    rw [hdeg v, hcl] at hsplit
    omega
  have hadj_card : ∀ v : V, Fintype.card {w : V // G.Adj v w} = k := by
    intro v
    calc
      Fintype.card {w : V // G.Adj v w} = Fintype.card (G.neighborSet v) :=
        Fintype.card_congr (Equiv.setCongr rfl)
      _ = G.degree v := G.card_neighborSet_eq_degree v
      _ = k := h.regular.degree_eq v
  have hnonadj_card : ∀ v : V,
      Fintype.card {w : V // v ≠ w ∧ ¬ G.Adj v w} = n - 1 - k := by
    intro v
    have hp : Fintype.card {w : V // w = v ∨ G.Adj v w} = k + 1 := by
      rw [Fintype.card_subtype]
      have hfilter :
          (Finset.univ.filter (fun w : V => w = v ∨ G.Adj v w)) =
            insert v (G.neighborFinset v) := by
        ext w
        simp [G.mem_neighborFinset, eq_comm]
      rw [hfilter, Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v)]
      rw [G.card_neighborFinset_eq_degree, h.regular.degree_eq]
    have hpred :
        ({w : V | v ≠ w ∧ ¬ G.Adj v w} : Set V) =
          {w : V | ¬ (w = v ∨ G.Adj v w)} := by
      ext w
      simp [eq_comm]
    calc
      Fintype.card {w : V // v ≠ w ∧ ¬ G.Adj v w} =
          Fintype.card {w : V // ¬ (w = v ∨ G.Adj v w)} :=
        Fintype.card_congr (Equiv.setCongr hpred)
      _ = Fintype.card V - Fintype.card {w : V // w = v ∨ G.Adj v w} :=
        Fintype.card_subtype_compl _
      _ = n - 1 - k := by rw [h.card, hp]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w hvw
    have hleft := hadj_left v w hvw
    have hright := hadj_left w v (G.adj_comm v w |>.mp hvw)
    have hcl : (G.neighborFinset v ∩ G.neighborFinset w).card = l :=
      (hcommon v w).trans (h.of_adj v w hvw)
    rw [hcl, hleft, hright]
  · intro v w hne hn
    have hleft := hnotadj_left v w hne hn
    have hright := hnotadj_left w v (Ne.symm hne) (by
      intro hwv
      exact hn (G.adj_comm w v |>.mp hwv))
    have hcl : (G.neighborFinset v ∩ G.neighborFinset w).card = μ :=
      (hcommon v w).trans (h.of_not_adj hne hn)
    rw [hcl, hleft, hright]
  · calc
      (∑ v : V, Fintype.card {w : V // G.Adj v w}) = ∑ _v : V, k := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hadj_card v
      _ = Fintype.card V * k := by simp
      _ = n * k := by rw [h.card]
  · calc
      (∑ v : V, Fintype.card {w : V // v ≠ w ∧ ¬ G.Adj v w}) =
          ∑ _v : V, (n - 1 - k) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hnonadj_card v
      _ = Fintype.card V * (n - 1 - k) := by simp
      _ = n * (n - 1 - k) := by rw [h.card]

end MathlibPlus.GraphTheory
