import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.GroupTheory.Claim31713

/-- The 2-closure relation is monotone in the underlying permutation group:
if `H ≤ X`, every ordered-pair witness from `H` is also a witness from `X`. -/
theorem inTwoClosure_mono
    {α : Type*} [Fintype α]
    {H X : Subgroup (Equiv.Perm α)} (hHX : H ≤ X)
    {q : Equiv.Perm α}
    (hq : MathlibPlus.GroupTheory.TwoClosure.inTwoClosure H q) :
    MathlibPlus.GroupTheory.TwoClosure.inTwoClosure X q := by
  intro x y
  obtain ⟨g, hg, hx, hy⟩ := hq x y
  exact ⟨g, hHX hg, hx, hy⟩

end MathlibPlus.GroupTheory.Claim31713
