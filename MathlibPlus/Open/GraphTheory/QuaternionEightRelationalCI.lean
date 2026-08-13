import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The quaternion group of order eight has the Cayley-isomorphism property for
arbitrarily many labelled directed binary relations. -/
def quaternionEightRelationalCI : Prop :=
  ∀ (κ : Type) (S T : κ → Set (QuaternionGroup 2))
      (e : QuaternionGroup 2 ≃ QuaternionGroup 2),
    (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
      ∃ φ : QuaternionGroup 2 ≃* QuaternionGroup 2,
        ∀ i, φ '' S i = T i

end MathlibPlus.Open.GraphTheory
