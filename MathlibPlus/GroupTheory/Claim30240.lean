import Mathlib

namespace MathlibPlus.GroupTheory

/-- An abstract isomorphism transports two regular permutation labelings to a
conjugating permutation.  The hypotheses spell out the regular labelings,
without introducing a source-specific finiteness or subgroup encoding. -/
theorem regularLabelingConjugacy_claim30240
    {G₁ G₂ Ω : Type*} [Group G₁] [Group G₂]
    (e : G₁ ≃* G₂)
    (ρ₁ : G₁ → Ω ≃ Ω) (ρ₂ : G₂ → Ω ≃ Ω)
    (ℓ₁ : G₁ ≃ Ω) (ℓ₂ : G₂ ≃ Ω)
    (h₁ : ∀ g h, ℓ₁ (g * h) = ρ₁ g (ℓ₁ h))
    (h₂ : ∀ g h, ℓ₂ (g * h) = ρ₂ g (ℓ₂ h)) :
    ∃ p : Ω ≃ Ω, ∀ g x, p (ρ₁ g x) = ρ₂ (e g) (p x) := by
  let p : Ω ≃ Ω := ℓ₁.symm.trans (e.toEquiv.trans ℓ₂)
  refine ⟨p, ?_⟩
  intro g x
  obtain ⟨h, rfl⟩ := ℓ₁.surjective x
  calc
    p (ρ₁ g (ℓ₁ h)) = p (ℓ₁ (g * h)) := by rw [h₁]
    _ = ℓ₂ (e (g * h)) := by simp [p]
    _ = ℓ₂ (e g * e h) := by rw [e.map_mul]
    _ = ρ₂ (e g) (ℓ₂ (e h)) := by rw [h₂]
    _ = ρ₂ (e g) (p (ℓ₁ h)) := by simp [p]

end MathlibPlus.GroupTheory
