import MathlibPlus.GroupTheory.TwoClosure

namespace MathlibPlus.GroupTheory.TwoClosure

variable {α : Type*}

/-- Membership in the binary two-closure is equivalent to preserving every
binary relation invariant under the original permutation group. -/
theorem inTwoClosure_iff_preserves_invariant_binaryRelations
    (G : Subgroup (Equiv.Perm α)) (q : Equiv.Perm α) :
    inTwoClosure G q ↔
      ∀ R : Set (α × α),
        (∀ g : Equiv.Perm α, g ∈ G → ∀ x y : α,
          ((x, y) ∈ R ↔ (g x, g y) ∈ R)) →
        ∀ x y : α, ((x, y) ∈ R ↔ (q x, q y) ∈ R) := by
  constructor
  · intro hq R hR x y
    obtain ⟨g, hg, hgx, hgy⟩ := hq x y
    simpa [hgx, hgy] using hR g hg x y
  · intro hpres x y
    let R : Set (α × α) :=
      {z | ∃ g : Equiv.Perm α, g ∈ G ∧ g x = z.1 ∧ g y = z.2}
    have hR : ∀ g : Equiv.Perm α, g ∈ G → ∀ u v : α,
        ((u, v) ∈ R ↔ (g u, g v) ∈ R) := by
      intro g hg u v
      constructor
      · rintro ⟨a, ha, hax, hay⟩
        refine ⟨g * a, G.mul_mem hg ha, ?_, ?_⟩
        · simp [Equiv.Perm.mul_apply, hax]
        · simp [Equiv.Perm.mul_apply, hay]
      · rintro ⟨a, ha, hax, hay⟩
        refine ⟨g⁻¹ * a, G.mul_mem (G.inv_mem hg) ha, ?_, ?_⟩
        · have hx := congrArg g.symm hax
          simpa [Equiv.Perm.mul_apply] using hx
        · have hy := congrArg g.symm hay
          simpa [Equiv.Perm.mul_apply] using hy
    have hxy : (x, y) ∈ R := ⟨1, G.one_mem, by simp, by simp⟩
    have hqxy : (q x, q y) ∈ R := (hpres R hR x y).mp hxy
    obtain ⟨g, hg, hgx, hgy⟩ := hqxy
    exact ⟨g, hg, hgx, hgy⟩

end MathlibPlus.GroupTheory.TwoClosure
