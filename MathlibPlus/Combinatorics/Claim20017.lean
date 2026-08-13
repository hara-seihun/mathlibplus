import Mathlib

namespace MathlibPlus.Combinatorics.Claim20017

open scoped BigOperators

universe u v

theorem injectiveSetUnionProduct_claim20017
    {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq α]
    (C : ι → Finset (Finset α))
    (h_empty : ∀ i, ∅ ∈ C i)
    (h_union : ∀ i A B, A ∈ C i → B ∈ C i → A ∪ B ∈ C i)
    (μ : (∀ i, C i) → Finset α)
    (hμ : ∀ x, μ x = Finset.univ.biUnion (fun i => (x i : Finset α)))
    (h_inj : Function.Injective μ) :
    Set.ncard (Set.range μ) = ∏ i, (C i).card ∧
      ∅ ∈ Set.range μ ∧
      (∀ A B, A ∈ Set.range μ → B ∈ Set.range μ →
        A ∪ B ∈ Set.range μ) := by
  classical
  have hcard : Set.ncard (Set.range μ) = ∏ i, (C i).card := by
    rw [Set.ncard_range_of_injective h_inj, Nat.card_pi]
    simp [Nat.card_eq_fintype_card]
  have hempty : ∅ ∈ Set.range μ := by
    let x : ∀ i, C i := fun i => ⟨∅, h_empty i⟩
    refine ⟨x, ?_⟩
    rw [hμ]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    simpa [x] using hai
  have hunion : ∀ A B, A ∈ Set.range μ → B ∈ Set.range μ →
      A ∪ B ∈ Set.range μ := by
    intro A B hA hB
    obtain ⟨x, rfl⟩ := hA
    obtain ⟨y, rfl⟩ := hB
    let z : ∀ i, C i := fun i =>
      ⟨(x i : Finset α) ∪ (y i : Finset α),
        h_union i (x i : Finset α) (y i : Finset α) (x i).property (y i).property⟩
    refine ⟨z, ?_⟩
    rw [hμ x, hμ y, hμ z]
    ext a
    simp only [z, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hxi | hyi⟩
      · exact Or.inl ⟨i, hxi⟩
      · exact Or.inr ⟨i, hyi⟩
    · rintro (⟨i, hxi⟩ | ⟨i, hyi⟩)
      · exact ⟨i, Or.inl hxi⟩
      · exact ⟨i, Or.inr hyi⟩
  exact ⟨hcard, hempty, hunion⟩

end MathlibPlus.Combinatorics.Claim20017
