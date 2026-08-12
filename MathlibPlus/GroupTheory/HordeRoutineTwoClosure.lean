import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory

/-!
Formalization of admitted claim 38568.  The two-closure and orbital predicates
are expanded in the theorem so that the inclusion has its exact pair-action
meaning without introducing a stronger ambient assertion.
-/

/-- If `H ≤ X`, every `X`-orbital is a union of `H`-orbitals, and the
corresponding two-closure inclusion holds. -/
theorem twoClosure_mono_claim38568
    {Ω : Type*} {H X : Subgroup (Equiv.Perm Ω)} (hHX : H ≤ X) :
    (let sameOrbital : Subgroup (Equiv.Perm Ω) → Ω → Ω → Ω → Ω → Prop :=
        fun K a b c d => ∃ k : K, k.1 a = c ∧ k.1 b = d
     let inTwoClosure : Subgroup (Equiv.Perm Ω) → Equiv.Perm Ω → Prop :=
        fun K g => ∀ a b : Ω, ∃ k : K, g a = k.1 a ∧ g b = k.1 b
     (∀ a b c d : Ω, sameOrbital H a b c d → sameOrbital X a b c d) ∧
       (∀ g : Equiv.Perm Ω,
         inTwoClosure H g → inTwoClosure X g)) := by
  dsimp
  constructor
  · intro a b c d h
    rcases h with ⟨k, hka, hkb⟩
    exact ⟨⟨k, hHX k.property⟩, hka, hkb⟩
  · intro g hg a b
    rcases hg a b with ⟨k, hka, hkb⟩
    exact ⟨⟨k, hHX k.property⟩, hka, hkb⟩

end MathlibPlus.GroupTheory
