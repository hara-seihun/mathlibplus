import Mathlib

namespace MathlibPlus.Algebra.Claim24747

/-- The pair-state polynomial from the ternary degree-two transfer has linear
coefficient `a + b - e - f` and constant coefficient `a*b - e*f`. -/
theorem pairStatePolynomial_degree_le_zero_iff_pairSums_eq
    (a b e f : ℚ) :
    (Polynomial.C (a + b - e - f) * Polynomial.X +
      Polynomial.C (a * b - e * f)).degree ≤ 0 ↔
      a + b = e + f := by
  constructor
  · intro h
    by_contra hsum
    have hcoeff :
        (Polynomial.C (a + b - e - f) * Polynomial.X +
          Polynomial.C (a * b - e * f)).coeff 1 = 0 := by
      have hlt : (Polynomial.C (a + b - e - f) * Polynomial.X +
          Polynomial.C (a * b - e * f)).degree < (1 : WithBot ℕ) := by
        exact lt_of_le_of_lt h (by norm_num)
      exact Polynomial.coeff_eq_zero_of_degree_lt hlt
    simp [Polynomial.coeff_add, Polynomial.coeff_mul_X] at hcoeff
    exact hsum (by linarith)
  · intro hsum
    rw [show a + b - e - f = 0 by linarith]
    simp only [Polynomial.C_0, zero_mul, zero_add]
    exact Polynomial.degree_C_le

/-- If the pair-state polynomial is nonzero, its degree is exactly zero
precisely when the pair sums agree; the product difference is the nonzero
constant term in that case. -/
theorem pairStatePolynomial_degree_eq_zero_iff
    (a b e f : ℚ) :
    (Polynomial.C (a + b - e - f) * Polynomial.X +
      Polynomial.C (a * b - e * f)).degree = 0 ↔
      a + b = e + f ∧ a * b ≠ e * f := by
  constructor
  · intro h
    have hle := le_of_eq h
    have hsum : a + b = e + f :=
      pairStatePolynomial_degree_le_zero_iff_pairSums_eq a b e f |>.mp hle
    have hpne : a * b - e * f ≠ 0 := by
      intro hp
      have hz : Polynomial.C (a + b - e - f) * Polynomial.X +
          Polynomial.C (a * b - e * f) = 0 := by
        rw [show a + b - e - f = 0 by linarith, hp]
        simp
      rw [hz] at h
      simp at h
    refine ⟨hsum, ?_⟩
    intro hprod
    apply hpne
    linarith
  · rintro ⟨hsum, hpne⟩
    rw [show a + b - e - f = 0 by linarith]
    simp only [Polynomial.C_0, zero_mul, zero_add]
    have hc : a * b - e * f ≠ 0 := by
      intro hzero
      apply hpne
      linarith
    rw [Polynomial.degree_C hc]

end MathlibPlus.Algebra.Claim24747
