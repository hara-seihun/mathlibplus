import Mathlib

/-!
# Homogeneous kernel relation

The source claim does not supply the carrier or specialization map.  The
kernel-checked core is stated for a ring homomorphism with the two displayed
terms both specializing to `z²`.
-/

namespace MathlibPlus.Algebra.Claim22963

/-- If both terms specialize to `z²`, their difference is in the kernel. -/
theorem homogeneousKernelRelation
    {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (o₁ o₂ : R) (z : S)
    (ho₂ : φ o₂ = z ^ 2)
    (ho₁sq : φ (o₁ ^ 2) = z ^ 2) :
    o₂ - o₁ ^ 2 ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker]
  rw [map_sub, ho₂, ho₁sq]
  exact sub_self _

end MathlibPlus.Algebra.Claim22963
