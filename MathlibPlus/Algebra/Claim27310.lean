import Mathlib

namespace MathlibPlus.Algebra.Claim27310

/-- Distinct powers of an indeterminate remain linearly independent after
multiplication by nonzero scalar coefficient polynomials.  This is the exact
`z`-degree core of the vertex-polynomial claim; the source's `A,B,C,D`
coefficient carriers are represented by nonzero elements of a domain. -/
theorem distinct_degree_vertex_polynomials_claim27310
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (K : ℕ) (q : Fin (K + 1) → R)
    (hq : ∀ i, q i ≠ 0) :
    LinearIndependent R
      (fun i : Fin (K + 1) =>
        Polynomial.C (q i) * Polynomial.X ^ (K - i.1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hc := congrArg
    (fun p : Polynomial R => p.coeff (K - i.1)) hsum
  have hcoeff : g i * q i = 0 := by
    rw [Polynomial.finsetSum_coeff] at hc
    simp only [Polynomial.coeff_smul, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, smul_eq_mul] at hc
    have hexp : ∀ x : Fin (K + 1), x ≠ i →
        K - i.1 ≠ K - x.1 := by
      intro x hxi heq
      apply hxi
      apply Fin.ext
      omega
    have hsum :
        (∑ x : Fin (K + 1),
          g x * (q x * if K - i.1 = K - x.1 then 1 else 0)) =
          g i * (q i * if K - i.1 = K - i.1 then 1 else 0) := by
      apply Finset.sum_eq_single i
      · intro x hx hxi
        simp [hexp x hxi]
      · simp
    rw [hsum] at hc
    simpa using hc
  exact (mul_eq_zero.mp hcoeff).resolve_right (hq i)

end MathlibPlus.Algebra.Claim27310
