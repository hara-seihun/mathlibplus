import Mathlib

namespace MathlibPlus.Algebra.MultiplierProfile

/-- A multiplier profile is aperiodic exactly when its scalar left stabilizer is
trivial.  Aperiodicity is expressed as the absence of a nonidentity left
period. -/
theorem multiplierProfile_aperiodic_iff_scalarLeftStabilizer_eq_singleton
    (p : ℕ) (_hp : Nat.Prime p)
    {H : Type*} [Group H]
    (multiplier : H → (ZMod p)ˣ) (τ : H → ZMod p) (_σ : H → H)
    (_hmultiplier : multiplier 1 = 1) (_hτ : τ 1 = 0) :
    (∀ g : H, g ≠ 1 → ∃ k : H, multiplier (g * k) ≠ multiplier k) ↔
      {g : H | ∀ k : H, multiplier (g * k) = multiplier k} = ({1} : Set H) := by
  constructor
  · intro haper
    apply Set.Subset.antisymm
    · intro g hg
      by_contra hne
      obtain ⟨k, hk⟩ := haper g hne
      exact hk (hg k)
    · intro g hg
      have hg1 : g = 1 := by simpa using hg
      subst g
      intro k
      simp
  · intro hQ g hgne
    by_contra hno
    have hgQ : ∀ k : H, multiplier (g * k) = multiplier k := by
      intro k
      by_contra hneq
      exact hno ⟨k, hneq⟩
    have hg_singleton : g ∈ ({1} : Set H) := by
      rw [← hQ]
      exact hgQ
    have hg1 : g = 1 := by simpa using hg_singleton
    exact hgne hg1

end MathlibPlus.Algebra.MultiplierProfile
