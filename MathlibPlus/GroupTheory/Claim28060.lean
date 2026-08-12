import Mathlib

namespace MathlibPlus.GroupTheory.Claim28060

/-- Claim 28060: transitivity with trivial point stabilizers is equivalent to
unique transport between every ordered pair of vertices. -/
theorem regularSubgroup_iff_uniqueTransport {V : Type*} [Fintype V]
    (H : Subgroup (Equiv.Perm V)) :
    ((∀ x y : V, ∃ σ : H, (σ : Equiv.Perm V) x = y) ∧
      (∀ x : V, ∀ σ τ : H,
        (σ : Equiv.Perm V) x = (τ : Equiv.Perm V) x → σ = τ)) ↔
      ∀ x y : V, ∃! σ : H, (σ : Equiv.Perm V) x = y := by
  constructor
  · rintro ⟨htrans, hfree⟩ x y
    rcases htrans x y with ⟨σ, hσ⟩
    refine ⟨σ, hσ, ?_⟩
    intro τ hτ
    exact hfree x τ σ (hτ.trans hσ.symm)
  · intro h
    constructor
    · intro x y
      exact (h x y).exists
    · intro x σ τ hστ
      exact (h x ((σ : Equiv.Perm V) x)).unique rfl hστ.symm

end MathlibPlus.GroupTheory.Claim28060
