import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

/-- Equality in the finite union-cardinality bound is equivalent to pairwise
 disjointness of the component supports. -/
theorem card_biUnion_eq_sum_iff_pairwiseDisjoint_claim23418
    {ι α : Type*} [DecidableEq α] (s : Finset ι) (f : ι → Finset α) :
    (s.biUnion f).card = (∑ i ∈ s, (f i).card) ↔
      (s : Set ι).PairwiseDisjoint f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      constructor
      · intro h
        have hle : (s.biUnion f).card ≤ ∑ i ∈ s, (f i).card :=
          Finset.card_biUnion_le
        have hu : (f a ∪ s.biUnion f).card ≤
            (f a).card + (s.biUnion f).card := Finset.card_union_le _ _
        have hsum : (s.biUnion f).card = ∑ i ∈ s, (f i).card := by
          omega
        have hcard : (f a ∪ s.biUnion f).card =
            (f a).card + (s.biUnion f).card := by
          omega
        have hdisj : Disjoint (f a) (s.biUnion f) :=
          (Finset.card_union_eq_card_add_card).mp hcard
        have hs : (s : Set ι).PairwiseDisjoint f := ih.mp hsum
        have hpair : (insert a (s : Set ι)).PairwiseDisjoint f := by
          refine (Set.pairwiseDisjoint_insert (α := Finset α) (ι := ι)
            (f := f) (i := a)).2 ⟨hs, ?_⟩
          intro b hb hne
          apply Finset.disjoint_left.mpr
          intro x hxa hxb
          apply (Finset.disjoint_left.mp hdisj) hxa
          exact Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩
        simpa only [Finset.coe_insert] using hpair
      · intro h
        have h' : (insert a (s : Set ι)).PairwiseDisjoint f := by
          simpa only [Finset.coe_insert] using h
        have hs := (Set.pairwiseDisjoint_insert (α := Finset α) (ι := ι)
          (f := f) (i := a)).1 h'
        have hdisj : Disjoint (f a) (s.biUnion f) := by
          apply Finset.disjoint_left.mpr
          intro x hxa hxU
          rcases Finset.mem_biUnion.mp hxU with ⟨b, hb, hxb⟩
          have hne : a ≠ b := by
            intro hab
            apply ha
            simpa [hab] using hb
          exact (Finset.disjoint_left.mp (hs.2 b hb hne)) hxa hxb
        rw [Finset.card_union_eq_card_add_card.mpr hdisj,
          Finset.card_biUnion hs.1]

end MathlibPlus.Combinatorics
