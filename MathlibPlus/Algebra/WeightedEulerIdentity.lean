import Mathlib

namespace MathlibPlus.Algebra

open scoped BigOperators
open MvPolynomial

/-!
# Weighted Euler identity for a finite polynomial jet

The source claim's tree and chromatic-symmetric-function interfaces are not
specified in the admitted text.  The formalization therefore keeps the exact
polynomial identity: a finite multivariate polynomial whose supported
monomials all have the same weighted degree satisfies weighted Euler's formula.
-/

/-- Weighted Euler's identity for a homogeneous multivariate polynomial over `ℚ`.
The `pderiv` terms are the first jet coordinates. -/
theorem weightedEulerIdentity
    {n : ℕ} (w : Fin n → ℕ) (d : ℕ)
    (p : MvPolynomial (Fin n) ℚ)
    (h : ∀ m ∈ p.support, ∑ i : Fin n, w i * m i = d) :
    (d : ℚ) • p = ∑ i : Fin n, (w i : ℚ) • (X i * pderiv i p) := by
  rw [p.as_sum]
  simp only [Finset.smul_sum, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [X_mul_pderiv_monomial]
  simp_rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  rw [← Finset.sum_smul]
  have hmdegq := congrArg (fun z : ℕ => (z : ℚ)) (h m hm)
  norm_num at hmdegq
  rw [hmdegq]

/-- When the common weighted degree is nonzero, the first jet reconstructs the
polynomial by the weighted Euler formula. -/
theorem weightedEulerReconstruction
    {n : ℕ} (w : Fin n → ℕ) (d : ℕ)
    (p : MvPolynomial (Fin n) ℚ)
    (hd : (d : ℚ) ≠ 0)
    (h : ∀ m ∈ p.support, ∑ i : Fin n, w i * m i = d) :
    p = (d : ℚ)⁻¹ • ∑ i : Fin n, (w i : ℚ) • (X i * pderiv i p) := by
  rw [← weightedEulerIdentity w d p h]
  simp [hd]

/-- Equality of the polynomial invariant forces equality of all its first
partial derivatives. -/
theorem polynomialDeterminesFirstPartials
    {n : ℕ} (p q : MvPolynomial (Fin n) ℚ)
    (hpq : p = q) :
    ∀ i : Fin n, pderiv i p = pderiv i q := by
  intro i
  rw [hpq]

end MathlibPlus.Algebra
