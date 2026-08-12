import Mathlib

namespace MathlibPlus.GroupTheory.Claim24148

/-- The complement of an index-two subgroup is closed under inversion. -/
theorem indexTwo_complement_inverseClosed_claim24148
    {G : Type*} [Group G] (H : Subgroup G) (_hindex : H.index = 2) :
    ∀ x : G, x ∉ H → x⁻¹ ∉ H := by
  intro x hx hxin
  apply hx
  simpa using H.inv_mem hxin

end MathlibPlus.GroupTheory.Claim24148
