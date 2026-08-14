import Mathlib

namespace MathlibPlus.NumberTheory.Claim9190

/-- A nonzero algebraic integer whose reciprocal is also an algebraic integer
is a unit of the ring of algebraic integers.  The integral closure is the
carrier that makes the algebraic-unit conclusion nontrivial. -/
theorem reciprocalAlgebraicInteger_isUnit_claim9190
    {K : Type*} [Field K] {α : K}
    (hα : IsIntegral ℤ α) (hα0 : α ≠ 0)
    (hαinv : IsIntegral ℤ α⁻¹) :
    IsUnit (⟨α, hα⟩ : integralClosure ℤ K) := by
  refine isUnit_iff_exists_inv.mpr ⟨⟨α⁻¹, hαinv⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ hα0

end MathlibPlus.NumberTheory.Claim9190
