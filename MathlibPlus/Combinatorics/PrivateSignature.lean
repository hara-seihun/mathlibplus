import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-- A private signature remains private after restricting the ambient set. -/
theorem private_signature_hereditary_claim14355
    {α β : Type*} (P : α → β → Prop) {R S : Set α}
    (_hR : R.Finite) (hSR : S ⊆ R) (Y : α) (_hY : Y ∈ S)
    (hprivate : ∃ σ, P Y σ ∧ ∀ Z, Z ∈ R → Z ≠ Y → ¬ P Z σ) :
    ∃ σ, P Y σ ∧ ∀ Z, Z ∈ S → Z ≠ Y → ¬ P Z σ := by
  obtain ⟨σ, hσY, hσprivate⟩ := hprivate
  exact ⟨σ, hσY, fun Z hZS hZY => hσprivate Z (hSR hZS) hZY⟩

end MathlibPlus.Combinatorics
