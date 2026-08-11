import Mathlib

namespace MathlibPlus.NumberTheory.Claim17060

/-- The explicit degree-ten integer polynomial appearing in the Lehmer claim. -/
noncomputable def lehmerPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 10 + Polynomial.X ^ 9 - Polynomial.X ^ 7 -
    Polynomial.X ^ 6 - Polynomial.X ^ 5 - Polynomial.X ^ 4 -
    Polynomial.X ^ 3 + Polynomial.X + 1

/-- The displayed polynomial has no coefficient above degree ten. -/
theorem lehmerPolynomial_natDegree_le :
    lehmerPolynomial.natDegree ≤ 10 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  simp only [lehmerPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  have h10 : N ≠ 10 := by omega
  have h9 : N ≠ 9 := by omega
  have h7 : N ≠ 7 := by omega
  have h6 : N ≠ 6 := by omega
  have h5 : N ≠ 5 := by omega
  have h4 : N ≠ 4 := by omega
  have h3 : N ≠ 3 := by omega
  have h1 : N ≠ 1 := by omega
  have h1' : (1 : ℕ) ≠ N := by omega
  have h0 : N ≠ 0 := by omega
  simp [h10, h9, h7, h6, h5, h4, h3, h1, h1', h0]

/-- Its leading nonzero coefficient is the coefficient of `X^10`. -/
theorem lehmerPolynomial_natDegree :
    lehmerPolynomial.natDegree = 10 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    lehmerPolynomial_natDegree_le
  simp only [lehmerPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

/-- The explicit Lehmer polynomial is monic. -/
theorem lehmerPolynomial_monic :
    lehmerPolynomial.Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one 10
    lehmerPolynomial_natDegree_le
  simp only [lehmerPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num

end MathlibPlus.NumberTheory.Claim17060
