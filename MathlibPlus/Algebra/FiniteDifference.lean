import Mathlib

namespace MathlibPlus.Algebra.FiniteDifference

/-- The exact linear-correction difference identity from admitted claim 56347.
The local difference operator is `Δ_u f x = f (x + u) - f x`; adding a
linear correction changes it by the constant `ℓ u`. -/
theorem linearCorrectionDifference_claim56347
    {R X D : Type*} [Ring R] [AddCommGroup X] [AddCommGroup D]
    [Module R X] [Module R D]
    (r s : X → D) (ell : X →ₗ[R] D)
    (h : ∀ z, r z = s z + ell z) (u x : X) :
    let Δ : (X → D) → X → X → D := fun f v z => f (z + v) - f z
    Δ r u x = Δ s u x + ell u := by
  dsimp
  rw [h (x + u), h x, map_add]
  abel

end MathlibPlus.Algebra.FiniteDifference
