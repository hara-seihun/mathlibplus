import MathlibPlus.Open.ResearchFormalization.Claim28870

namespace MathlibPlus.Open.ResearchFormalization.Claim28871

open MathlibPlus.Open.ResearchFormalization.Claim28870

/-- Oddness transports the normalized derivative witnesses from the four sign
representatives to their negatives, and those signed representatives exhaust
all nonzero points of the ternary plane. -/
def derivativeSymmetryAndNegativeWitnessCoverage_claim28871 : Prop :=
  (∀ (V : Type*) [AddCommGroup V] [Module Ternary V]
      [FiniteDimensional Ternary V],
      ∀ f : Plane → V,
        (∀ y : Plane, f (-y) = -f y) →
          ∀ a c x : Plane,
            normalizedDerivative f a c (-x) =
              normalizedDerivative f a (-c - a) x) ∧
    (Fintype.card {x : Plane // x ≠ 0} = 8 ∧
      Finset.univ.filter (fun x : Plane => x ≠ 0) =
        ({e₁, -e₁, e₂, -e₂, e₁ + e₂, -(e₁ + e₂), e₁ - e₂,
          -(e₁ - e₂)} : Finset Plane)) ∧
    (∀ (V : Type*) [AddCommGroup V] [Module Ternary V]
      [FiniteDimensional Ternary V],
      ∀ g : Plane → V, normalizedMap g →
        let A := g (e₁ + e₂)
        let B := g (e₁ - e₂)
        ∀ x : Plane, x ≠ 0 →
          (∃ a c : Plane, normalizedDerivative g a c x = A) ∧
            (∃ a c : Plane, normalizedDerivative g a c x = B))

end MathlibPlus.Open.ResearchFormalization.Claim28871
