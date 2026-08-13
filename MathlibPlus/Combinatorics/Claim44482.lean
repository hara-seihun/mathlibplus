import Mathlib

open scoped BigOperators

private lemma pairwiseDisjoint_of_card_biUnion_eq_sum
    {ι V : Type*} [DecidableEq V]
    {s : Finset ι} (f : ι → Finset V)
    (h : (s.biUnion f).card = ∑ i ∈ s, (f i).card) :
    (s : Set ι).PairwiseDisjoint f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have h' :
          ((insert a s).biUnion f).card = (f a).card + ∑ i ∈ s, (f i).card := by
        simpa [Finset.biUnion_insert, Finset.sum_insert, ha] using h
      have htail_le :
          (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card := by
        exact Finset.card_biUnion_le
      have hunion_le :
          ((f a) ∪ (s.biUnion f)).card ≤ (f a).card + (s.biUnion f).card := by
        exact Finset.card_union_le _ _
      have h'le :
          ((insert a s).biUnion f).card ≤ (f a).card + (s.biUnion f).card := by
        simpa [Finset.biUnion_insert] using hunion_le
      have htail : (s.biUnion f).card = ∑ i ∈ s, (f i).card := by
        omega
      have hdisj : Disjoint (f a) (s.biUnion f) := by
        apply Finset.card_union_eq_card_add_card.mp
        calc
          ((f a) ∪ (s.biUnion f)).card =
              ((insert a s).biUnion f).card := by rw [Finset.biUnion_insert]
          _ = (f a).card + ∑ i ∈ s, (f i).card := h'
          _ = (f a).card + (s.biUnion f).card := by rw [htail]
      have ih' : (s : Set ι).PairwiseDisjoint f := ih htail
      intro i hi j hj hij
      rcases Finset.mem_insert.mp hi with hiA | hiS
      · rcases Finset.mem_insert.mp hj with hjA | hjS
        · exfalso
          exact hij (hiA.trans hjA.symm)
        · subst i
          apply Finset.disjoint_left.mpr
          intro x hxa hxj
          exact (Finset.disjoint_left.mp hdisj) hxa
            ((Finset.subset_biUnion_of_mem f hjS) hxj)
      · rcases Finset.mem_insert.mp hj with hjA | hjS
        · subst j
          apply Finset.disjoint_left.mpr
          intro x hxi hxa
          exact (Finset.disjoint_left.mp hdisj) hxa
            ((Finset.subset_biUnion_of_mem f hiS) hxi)
        · exact ih' hiS hjS hij

namespace MathlibPlus.Combinatorics

/-- Under the cardinality equality, covering the host is equivalent to disjoint actual supports. -/
theorem spanning_iff_pairwiseDisjointOf_sum_card_eq_claim44482
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (U : ι → Finset V)
    (hcard : ∑ i, (U i).card = Fintype.card V) :
    (⋃ i, (U i : Set V) = Set.univ) ↔
      (Set.univ : Set ι).PairwiseDisjoint U := by
  classical
  constructor
  · intro hu
    have hU : Finset.univ.biUnion U = (Finset.univ : Finset V) := by
      ext v
      have hv := Set.ext_iff.mp hu v
      simpa [Finset.mem_biUnion] using hv
    have hsum :
        (Finset.univ.biUnion U).card =
          ∑ i ∈ (Finset.univ : Finset ι), (U i).card := by
      rw [hU]
      simpa using hcard.symm
    simpa using (pairwiseDisjoint_of_card_biUnion_eq_sum U hsum)
  · intro hd
    have hd' : (↑(Finset.univ : Finset ι) : Set ι).PairwiseDisjoint U := by
      simpa using hd
    have hbi_card : (Finset.univ.biUnion U).card = Fintype.card V := by
      rw [Finset.card_biUnion hd']
      simpa using hcard
    have hU : Finset.univ.biUnion U = (Finset.univ : Finset V) :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        (by simpa using hbi_card.symm.le)
    ext v
    have hv := Finset.ext_iff.mp hU v
    simpa [Finset.mem_biUnion] using hv

end MathlibPlus.Combinatorics
