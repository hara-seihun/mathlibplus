import Batteries
import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.GroupTheory.TwoClosure

variable {α : Type*}

/-- The identity permutation belongs to every binary two-closure. -/
theorem inTwoClosure_one (G : Subgroup (Equiv.Perm α)) :
    inTwoClosure G 1 := by
  intro x y
  exact ⟨1, G.one_mem, by simp, by simp⟩

/-- Binary two-closure membership is closed under composition. -/
theorem inTwoClosure_mul (G : Subgroup (Equiv.Perm α))
    {q r : Equiv.Perm α} (hq : inTwoClosure G q) (hr : inTwoClosure G r) :
    inTwoClosure G (r * q) := by
  intro x y
  obtain ⟨g, hg, hgx, hgy⟩ := hq x y
  obtain ⟨h, hh, hhx, hhy⟩ := hr (q x) (q y)
  refine ⟨h * g, G.mul_mem hh hg, ?_, ?_⟩
  · simpa [Equiv.Perm.mul_apply, hgx] using hhx
  · simpa [Equiv.Perm.mul_apply, hgy] using hhy

/-- Binary two-closure membership is closed under inversion. -/
theorem inTwoClosure_inv (G : Subgroup (Equiv.Perm α))
    {q : Equiv.Perm α} (hq : inTwoClosure G q) :
    inTwoClosure G q⁻¹ := by
  intro x y
  obtain ⟨g, hg, hgx, hgy⟩ := hq (q⁻¹ x) (q⁻¹ y)
  refine ⟨g⁻¹, G.inv_mem hg, ?_, ?_⟩
  · apply g.injective
    simpa using hgx.symm
  · apply g.injective
    simpa using hgy.symm

/-- Enlarging the acting group can only enlarge its binary two-closure. -/
theorem inTwoClosure_mono
    {G H : Subgroup (Equiv.Perm α)} (hGH : G ≤ H)
    {q : Equiv.Perm α} (hq : inTwoClosure G q) :
    inTwoClosure H q := by
  intro x y
  obtain ⟨g, hg, hgx, hgy⟩ := hq x y
  exact ⟨g, hGH hg, hgx, hgy⟩

end MathlibPlus.GroupTheory.TwoClosure
