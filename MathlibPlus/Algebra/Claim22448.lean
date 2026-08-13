import Mathlib

open Polynomial

namespace MathlibPlus.Algebra.Claim22448

/-- A polynomial supported in degrees `d - h` through `d - 1` factors as
`Y^(d-h) Q`, with the quotient supported below degree `h`.  This is the
post-`a = 0` algebraic content of the higher-depth normal-layer compression;
the source's normal-layer construction is represented by the coefficient
support hypotheses. -/
theorem normal_layer_compression_claim22448
    {R : Type*} [Field R] (d h : ℕ) (E : R[X])
    (hhd : h < d)
    (hzero : ∀ k < d - h, E.coeff k = 0)
    (hdeg : E.natDegree < d) :
    ∃ Q : R[X], E = X ^ (d - h) * Q ∧
      Q.degree ≤ ((h - 1 : ℕ) : WithBot ℕ) := by
  have hdiv : X ^ (d - h) ∣ E :=
    (Polynomial.X_pow_dvd_iff).2 hzero
  rcases hdiv with ⟨Q, hEQ⟩
  refine ⟨Q, hEQ, ?_⟩
  by_cases hQ : Q = 0
  · simp [hQ]
  · apply Polynomial.natDegree_le_iff_degree_le.1
    rw [hEQ, Polynomial.natDegree_X_pow_mul _ hQ] at hdeg
    have hQdeg : Q.natDegree < h := by omega
    omega

end MathlibPlus.Algebra.Claim22448
