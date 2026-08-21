import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim27970

/-- For the concrete C₂³ first factor and an arbitrary permutation σ, the
pure-product normalized derivative has the displayed first coordinate and
retains the B-coordinate, without assuming B commutative. -/
theorem pure_product_normalized_derivative
    {B : Type*} [Group B]
    (σ : (Fin 3 → ZMod 2) ≃ (Fin 3 → ZMod 2))
    (x u : Fin 3 → ZMod 2) (b t : B) :
    (σ.symm (σ (x + u) + σ u), (b * t) * t⁻¹) =
      (σ.symm (σ (x + u) + σ u), b) := by
  rw [mul_inv_cancel_right]

end MathlibPlus.GroupTheory.Claim27970
