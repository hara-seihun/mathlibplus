import Mathlib

namespace MathlibPlus.GroupTheory

/-- Equality on every block of a common covering block system implies equality
of the two global permutations.  The source's quaternion subgroup data only
identify the two permutations; the implication itself uses the block cover. -/
theorem blockwise_restrictions_eq_global_claim38312
    {α : Type*}
    (u v : Equiv.Perm α) (blocks : Set (Set α))
    (hcover : ∀ x : α, ∃ B ∈ blocks, x ∈ B)
    (hrestr : ∀ B ∈ blocks, ∀ x ∈ B, u x = v x) :
    u = v := by
  ext x
  obtain ⟨B, hB, hxB⟩ := hcover x
  exact hrestr B hB x hxB

end MathlibPlus.GroupTheory
