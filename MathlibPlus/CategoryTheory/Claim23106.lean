import MathlibPlus.Basic

namespace MathlibPlus.CategoryTheory.Claim23106

/-- Separate input/output injectivity is compatible with an identity cospan.
The identity map witnesses this compatibility. -/
theorem separate_identity_cospan_is_injective (I : Type*) :
    ∃ f : I → I, Function.Injective f ∧ Function.Injective f := by
  exact ⟨id, Function.injective_id, Function.injective_id⟩

/-- The identity cospan cannot have an injective combined input/output map when
there is a port: both copies of a port map to the same vertex. -/
theorem identity_cospan_combined_injective_impossible
    {I V : Type*} [Nonempty I]
    (f : I → V)
    (combined : Sum I I → V)
    (hcombined : ∀ i, combined (Sum.inl i) = f i)
    (hcombined' : ∀ i, combined (Sum.inr i) = f i)
    (hinj : Function.Injective combined) : False := by
  let i : I := Classical.choice ‹Nonempty I›
  have heq : combined (Sum.inl i) = combined (Sum.inr i) := by
    rw [hcombined, hcombined']
  have hneq : (Sum.inl i : Sum I I) ≠ Sum.inr i := by
    simp
  exact hneq (hinj heq)

end MathlibPlus.CategoryTheory.Claim23106
