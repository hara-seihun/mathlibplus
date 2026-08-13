import Mathlib

namespace MathlibPlus.GroupTheory.Claim31849

/-- A support avoiding the identity is disjoint from its setwise left stabilizer.
The left stabilizer is written out as preservation of membership under every
left multiplication, matching the support-level statement. -/
theorem support_disjoint_leftStabilizer_claim31849
    {G : Type*} [Group G] (N : Set G) (hidentity : (1 : G) ∉ N) :
    N ∩ {g : G | ∀ x : G, x ∈ N ↔ g * x ∈ N} = (∅ : Set G) := by
  ext g
  constructor
  · rintro ⟨hg, hstab⟩
    have h1 : (1 : G) ∈ N := by
      apply (hstab 1).mpr
      simpa using hg
    exact (hidentity h1).elim
  · intro hg
    simp at hg

end MathlibPlus.GroupTheory.Claim31849
