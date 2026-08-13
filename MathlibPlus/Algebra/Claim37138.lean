import Mathlib

open Polynomial

namespace MathlibPlus.Algebra.Claim37138

/-- The shifted-trace coefficient relation, with the trace-zero condition
represented by the kernel equation for `X * J * C`. -/
theorem shiftedTrace_zero_relation
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (Φ : R[X] →ₗ[R] M) (Cpoly : R[X])
    (j₀ j₁ j₂ : R)
    (hzero : Φ (Polynomial.X *
        (Polynomial.C j₀ + Polynomial.C j₁ * Polynomial.X +
          Polynomial.C j₂ * Polynomial.X ^ 2) * Cpoly) = 0) :
    j₀ • Φ (Polynomial.X * Cpoly) +
      j₁ • Φ (Polynomial.X ^ 2 * Cpoly) +
      j₂ • Φ (Polynomial.X ^ 3 * Cpoly) = 0 := by
  have hp : Polynomial.X *
        (Polynomial.C j₀ + Polynomial.C j₁ * Polynomial.X +
          Polynomial.C j₂ * Polynomial.X ^ 2) * Cpoly =
      j₀ • (Polynomial.X * Cpoly) +
        j₁ • (Polynomial.X ^ 2 * Cpoly) +
        j₂ • (Polynomial.X ^ 3 * Cpoly) := by
    simp only [Polynomial.smul_eq_C_mul]
    ring
  rw [hp] at hzero
  simpa only [map_add, map_smul] using hzero

end MathlibPlus.Algebra.Claim37138
