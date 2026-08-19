import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Claim 29017: an additive one-cocycle can be changed by a coboundary so
that it vanishes at an element whose action-minus-identity is invertible. -/
def cocycleNormalization_claim29017 : Prop :=
  ∀ {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G → V →+ V) (f : G → V) (σ : G),
    (ρ 1 = AddMonoidHom.id V) ∧
    (∀ g h, ρ (g * h) = (ρ g).comp (ρ h)) →
    (∀ g h, f (g * h) = f g + ρ g (f h)) →
    (e : V ≃+ V) →
    (∀ x, e x = ρ σ x - x) →
    ∃ (v : V) (f' : G → V),
      (∀ g h, f' (g * h) = f' g + ρ g (f' h)) ∧
      (∀ g, f' g = f g - (ρ g v - v)) ∧
      f' σ = 0

end MathlibPlus.Open.GroupTheory
