import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.GroupTheory

open TwoClosure

/-- A two-transitive permutation group has the full symmetric group as its
2-closure, in the ordered-pair formulation used by `inTwoClosure`. -/
theorem twoTransitive_inTwoClosure_claim38567
    {α : Type*} [Fintype α]
    (X : Subgroup (Equiv.Perm α))
    (htrans : ∀ ⦃x y u v : α⦄, x ≠ y → u ≠ v →
      ∃ g : Equiv.Perm α, g ∈ X ∧ g x = u ∧ g y = v) :
    ∀ q : Equiv.Perm α, inTwoClosure X q := by
  intro q x y
  by_cases hxy : x = y
  · subst y
    rcases subsingleton_or_nontrivial α with hα | hα
    · letI := hα
      refine ⟨1, X.one_mem, ?_, ?_⟩
      · exact Subsingleton.elim _ _
      · exact Subsingleton.elim _ _
    · letI := hα
      obtain ⟨z, hz⟩ := exists_ne x
      have hqz : q z ≠ q x := by
        intro h
        exact hz (q.injective h)
      obtain ⟨g, hg, gz, gx⟩ := htrans hz hqz
      exact ⟨g, hg, gx, gx⟩
  · have hqxy : q x ≠ q y := by
      intro h
      apply hxy
      exact q.injective h
    obtain ⟨g, hg, gx, gy⟩ := htrans hxy hqxy
    exact ⟨g, hg, gx, gy⟩

end MathlibPlus.GroupTheory
