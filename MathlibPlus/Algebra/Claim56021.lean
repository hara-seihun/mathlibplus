import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim56021

/-- A mixed finite difference of a bilinear product, after any additive
measurement `τ₂`, is the measurement of the product of the two differences. -/
theorem mixedFiniteDifference
    {R : Type _} [Ring R] (τ₂ : R →+ R)
    (P P' Q Q' : R) :
    let E : R → R → R := fun A B => τ₂ (A * B)
    E P Q + E P' Q' - E P Q' - E P' Q =
      τ₂ ((P - P') * (Q - Q')) := by
  dsimp
  calc
    τ₂ (P * Q) + τ₂ (P' * Q') - τ₂ (P * Q') - τ₂ (P' * Q) =
        τ₂ (P * Q + P' * Q' - P * Q' - P' * Q) := by
          simp only [map_add, map_sub]
    _ = τ₂ ((P - P') * (Q - Q')) := by
      exact congrArg τ₂ (by noncomm_ring)

end MathlibPlus.Algebra.Claim56021
