import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card

namespace MathlibPlus.Combinatorics

universe u v

/-- Claim 44056: relabeling commutes with insertion of a certified outside
 element into a rank-`k` finite subset. -/
theorem booleanRankEquiv_insertOutside
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (relabel : α ≃ β)
    {k : ℕ}
    (subset : {s : Finset α // s.card = k})
    (outside : ↥((Finset.univ : Finset α) \ subset.1)) :
    (show {s : Finset β // s.card = k + 1} from
      ⟨(insert outside.1 subset.1).map relabel.toEmbedding,
        by
          rw [Finset.card_map, Finset.card_insert_of_notMem]
          · rw [subset.2]
          · exact (Finset.mem_sdiff.mp outside.2).2⟩)
      =
    (show {s : Finset β // s.card = k + 1} from
      ⟨insert (relabel outside.1)
          (subset.1.map relabel.toEmbedding),
        by
          rw [Finset.card_insert_of_notMem, Finset.card_map]
          · rw [subset.2]
          · intro h
            rcases Finset.mem_map.1 h with ⟨a, ha, haeq⟩
            have hEq : a = outside.1 := by
              apply relabel.injective
              exact haeq
            exact (Finset.mem_sdiff.mp outside.2).2 (hEq ▸ ha)⟩) := by
  apply Subtype.ext
  change
    (insert outside.1 subset.1).map relabel.toEmbedding =
      insert (relabel outside.1) (subset.1.map relabel.toEmbedding)
  exact Finset.map_insert _ _ _

end MathlibPlus.Combinatorics
