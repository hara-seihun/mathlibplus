import Mathlib

namespace MathlibPlus.GroupTheory

/-- The coupled inverse condition forced when a bijection sends an
inverse-closed set to an inverse-closed set (claim 35724). -/
theorem coupledInverseClosure_claim35724
    {G : Type*} [Group G] (f : G ≃ G) (_hf : f 1 = 1) (S : Set G)
    (_hS : ∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S)
    (hT : ∀ ⦃y : G⦄, y ∈ f '' S → y⁻¹ ∈ f '' S) :
    ∀ ⦃x : G⦄, x ∈ S → f.symm ((f x)⁻¹) ∈ S := by
  intro x hx
  have hxi : (f x)⁻¹ ∈ f '' S := hT ((Set.mem_image f S (f x)).2 ⟨x, hx, rfl⟩)
  rcases hxi with ⟨y, hy, hfy⟩
  rw [← hfy, f.symm_apply_apply]
  exact hy

end MathlibPlus.GroupTheory
