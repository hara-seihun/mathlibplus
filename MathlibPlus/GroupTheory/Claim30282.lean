import Mathlib

namespace MathlibPlus.GroupTheory.Claim30282

/-- A proper left-translate of a nonempty finite subset of a finite group
cannot be contained in that subset. -/
theorem exists_mul_not_mem_of_not_stabilizer
    {G : Type} [Fintype G] [Group G] [DecidableEq G]
    (N : Finset G) (_hN : N.Nonempty) {h : G}
    (hh : h ∉ {g : G | N.image (fun a => g * a) = N}) :
    ∃ a ∈ N, h * a ∉ N := by
  classical
  by_contra hcontra
  push Not at hcontra
  apply hh
  apply Finset.eq_of_subset_of_card_le
  · exact (Finset.image_subset_iff).2 hcontra
  · have hcard : (N.image (fun a => h * a)).card = N.card :=
      Finset.card_image_of_injective N (fun a b hab => mul_left_cancel hab)
    exact hcard.ge

/-- The chart consequence, expressed with the source's definition of `N` as
exactly the nontranslation indices. -/
theorem sourceProductChart_separation
    {G : Type} [Fintype G] [Group G] [DecidableEq G]
    (N : Finset G) (_hN : N.Nonempty) {h : G}
    (IsTranslation : G → Prop)
    (hNdef : ∀ a : G, a ∈ N ↔ ¬ IsTranslation a)
    (hh : h ∉ {g : G | N.image (fun a => g * a) = N}) :
    ∃ a ∈ N, IsTranslation (h * a) ∧ ¬ IsTranslation a := by
  obtain ⟨a, ha, hha⟩ := exists_mul_not_mem_of_not_stabilizer N _hN hh
  have htrans : IsTranslation (h * a) := by
    by_contra hnot
    exact hha ((hNdef (h * a)).2 hnot)
  exact ⟨a, ha, htrans, (hNdef a).1 ha⟩

end MathlibPlus.GroupTheory.Claim30282
