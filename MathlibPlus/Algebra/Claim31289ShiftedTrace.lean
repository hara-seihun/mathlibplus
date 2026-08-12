import Mathlib

namespace MathlibPlus.Algebra.Claim31289

/-- The shifted-trace identity from claim 31289.  The source's
root-forgetting map is represented by an arbitrary `R`-linear map on
`Polynomial R`; the finite polynomial `H` is written explicitly. -/
theorem shiftedTraceIdentity
    {R : Type*} [CommSemiring R] {q : ℕ}
    (Φ : Polynomial R →ₗ[R] R) (C : Polynomial R)
    (h : Fin (q + 1) → R) :
    Φ (Polynomial.X * C *
        ∑ a : Fin (q + 1), Polynomial.X ^ (a : ℕ) * Polynomial.C (h a)) =
      ∑ a : Fin (q + 1),
        h a * Φ (Polynomial.X ^ ((a : ℕ) + 1) * C) := by
  have hpoly :
      Polynomial.X * C *
          ∑ a : Fin (q + 1), Polynomial.X ^ (a : ℕ) * Polynomial.C (h a) =
        ∑ a : Fin (q + 1),
          h a • (Polynomial.X ^ ((a : ℕ) + 1) * C) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [pow_succ, Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul]
  rfl

end MathlibPlus.Algebra.Claim31289
