import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 26813: a central-equivariant bijection transports the right-translate
Cayley relation after adjoining the central involution. -/
def centralEquivariantCayleyAugmentation : Prop :=
  ∀ {G : Type*} [Group G] (c : G),
    c * c = 1 →
    c ≠ 1 →
    (∀ g : G, c * g = g * c) →
    (S T : Set G) →
    (Φ : G ≃ G) →
    (∀ x y : G,
      (∃ s ∈ S, y = x * s) ↔
        (∃ t ∈ T, Φ y = Φ x * t)) →
    (∀ x : G, Φ (c * x) = c * Φ x) →
    ∀ x y : G,
      (∃ s ∈ insert c S, y = x * s) ↔
        (∃ t ∈ insert c T, Φ y = Φ x * t)

end MathlibPlus.Combinatorics
