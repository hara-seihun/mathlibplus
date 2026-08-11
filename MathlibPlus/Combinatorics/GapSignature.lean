import Mathlib

namespace MathlibPlus.Combinatorics.GapSignature

/-- A target containing `V` is recovered from its gap over `V`. -/
theorem target_eq_of_gap_eq
    {α : Type*} {V U₁ U₂ : Set α}
    (hV₁ : V ⊆ U₁) (hV₂ : V ⊆ U₂)
    (hgap : U₁ \ V = U₂ \ V) : U₁ = U₂ := by
  ext x
  constructor
  · intro hx
    by_cases hxV : x ∈ V
    · exact hV₂ hxV
    · have hxgap : x ∈ U₁ \ V := ⟨hx, hxV⟩
      have hxgap' : x ∈ U₂ \ V := by
        rw [← hgap]
        exact hxgap
      exact hxgap'.1
  · intro hx
    by_cases hxV : x ∈ V
    · exact hV₁ hxV
    · have hxgap : x ∈ U₂ \ V := ⟨hx, hxV⟩
      have hxgap' : x ∈ U₁ \ V := by
        rw [hgap]
        exact hxgap
      exact hxgap'.1

/-- Distinct strict extensions of a reused descendant have distinct, nonempty
and ambiently contained gap signatures. -/
theorem gap_signature_pair
    {α : Type*} {Z Y_c V U₁ U₂ : Set α}
    (hV₁ : V ⊂ U₁) (hV₂ : V ⊂ U₂)
    (hambient₁ : U₁ ⊆ Z ∪ Y_c) (hambient₂ : U₂ ⊆ Z ∪ Y_c)
    (htargets_ne : U₁ ≠ U₂) :
    (U₁ \ V).Nonempty ∧
      (U₂ \ V).Nonempty ∧
      (U₁ \ V) ⊆ (Z ∪ Y_c) \ V ∧
      (U₂ \ V) ⊆ (Z ∪ Y_c) \ V ∧
      U₁ \ V ≠ U₂ \ V := by
  have hV₁' : V ⊆ U₁ := (Set.ssubset_iff_subset_ne.mp hV₁).1
  have hV₂' : V ⊆ U₂ := (Set.ssubset_iff_subset_ne.mp hV₂).1
  have hnot₁ : ¬U₁ ⊆ V := by
    intro h₁
    apply (Set.ssubset_iff_subset_ne.mp hV₁).2
    exact Set.Subset.antisymm hV₁' h₁
  have hnot₂ : ¬U₂ ⊆ V := by
    intro h₂
    apply (Set.ssubset_iff_subset_ne.mp hV₂).2
    exact Set.Subset.antisymm hV₂' h₂
  have hnonempty₁ : (U₁ \ V).Nonempty := Set.sdiff_nonempty.mpr hnot₁
  have hnonempty₂ : (U₂ \ V).Nonempty := Set.sdiff_nonempty.mpr hnot₂
  have hsubset₁ : (U₁ \ V) ⊆ (Z ∪ Y_c) \ V := by
    intro x hx
    exact ⟨hambient₁ hx.1, hx.2⟩
  have hsubset₂ : (U₂ \ V) ⊆ (Z ∪ Y_c) \ V := by
    intro x hx
    exact ⟨hambient₂ hx.1, hx.2⟩
  refine ⟨hnonempty₁, hnonempty₂, hsubset₁, hsubset₂, ?_⟩
  intro hgap
  apply htargets_ne
  exact target_eq_of_gap_eq hV₁' hV₂' hgap

end MathlibPlus.Combinatorics.GapSignature
