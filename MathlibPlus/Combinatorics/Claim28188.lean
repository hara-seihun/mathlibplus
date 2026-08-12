import Mathlib

namespace MathlibPlus.Combinatorics.Claim28188

/-- Transporting every paired orbital transports every fusion of those orbitals. -/
theorem image_iUnion_of_pairwise_transported
    {α β ι : Type*} (e : α ≃ β)
    (source : ι → Set α) (target : ι → Set β)
    (htransport : ∀ i, e '' source i = target i) (J : Set ι) :
    e '' (⋃ i ∈ J, source i) = ⋃ i ∈ J, target i := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨i, hi, hxi⟩
    refine ⟨i, hi, ?_⟩
    rw [← htransport i]
    exact ⟨x, hxi, rfl⟩
  · intro hy
    simp only [Set.mem_iUnion] at hy
    rcases hy with ⟨i, hi, hyi⟩
    rw [← htransport i] at hyi
    rcases hyi with ⟨x, hxi, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, hxi⟩

end MathlibPlus.Combinatorics.Claim28188
