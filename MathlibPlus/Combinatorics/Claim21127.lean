import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim21127

/-- Intersecting all coordinate sets recovers the distinguished singleton
point. -/
theorem singletonIntersection_reconstruct_claim21127
    {ι α : Type*} (I : ι → Set α) (y : α)
    (hI : ⋂ j, I j = ({y} : Set α)) :
    ∀ x : α, (∀ j, x ∈ I j) ↔ x = y := by
  intro x
  rw [← Set.mem_iInter]
  rw [hI]
  simp

end MathlibPlus.Combinatorics.Claim21127
