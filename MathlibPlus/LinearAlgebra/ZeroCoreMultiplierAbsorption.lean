import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 33303: a multiplier whose displacement has zero image is the
identity.  The ambient normalizer membership is retained as an explicit
parameter; no further property of the ambient set is needed for this case. -/
theorem zeroCoreMultiplierAbsorption
    {R W : Type*} [Semiring R] [AddCommGroup W] [Module R W]
    (N : Set (W →ₗ[R] W)) (M : W →ₗ[R] W) (_hMN : M ∈ N)
    (V : Submodule R W) (hV : V = ⊥)
    (hM : LinearMap.range (M - (LinearMap.id : W →ₗ[R] W)) ≤ V) :
    M = (LinearMap.id : W →ₗ[R] W) := by
  apply LinearMap.ext
  intro x
  have hx : (M - (LinearMap.id : W →ₗ[R] W)) x ∈ V := hM ⟨x, rfl⟩
  rw [hV] at hx
  have hz : (M - (LinearMap.id : W →ₗ[R] W)) x = 0 := by simpa using hx
  exact sub_eq_zero.mp hz

end MathlibPlus.LinearAlgebra
