import Mathlib

namespace MathlibPlus.Algebra.Claim14826

/-- The coefficient formula for the two-scale product, with the conditional
terms implementing the extension-by-zero convention outside `0 ≤ j ≤ 11`. -/
theorem twoScaleCoefficientFormula
    {R : Type*} [CommSemiring R]
    (b : ℕ → R → R)
    (hfamily : ∀ (A : R) (k : ℕ),
      b k A =
        (((1 + Polynomial.X) ^ 11) *
          (1 + Polynomial.C A * Polynomial.X) ^ 2).coeff k)
    (A : R) (k : ℕ) :
    b k A =
      (Nat.choose 11 k : R) +
        (if 1 ≤ k then
          (2 : R) * A * (Nat.choose 11 (k - 1) : R) else 0) +
        (if 2 ≤ k then
          A ^ 2 * (Nat.choose 11 (k - 2) : R) else 0) := by
  have hshift (c : R) (n : ℕ) :
      ((((1 + Polynomial.X) ^ 11) *
        (Polynomial.C c * Polynomial.X ^ n)).coeff k) =
        c * (if n ≤ k then (Nat.choose 11 (k - n) : R) else 0) := by
    have hcomm :
        ((1 + Polynomial.X) ^ 11) *
            (Polynomial.C c * Polynomial.X ^ n) =
          Polynomial.C c * (((1 + Polynomial.X) ^ 11) *
            Polynomial.X ^ n) := by
      ring
    rw [hcomm, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    simp [Polynomial.coeff_one_add_X_pow]
  have hquad :
      (1 + Polynomial.C A * Polynomial.X) ^ 2 =
        1 + Polynomial.C (2 * A) * Polynomial.X +
          Polynomial.C (A ^ 2) * Polynomial.X ^ 2 := by
    have htwo : (Polynomial.C (2 * A) : Polynomial R) = 2 * Polynomial.C A := by
      rw [Polynomial.C_mul, Polynomial.C_ofNat]
    have hsq : (Polynomial.C (A ^ 2) : Polynomial R) = (Polynomial.C A) ^ 2 := by
      rw [Polynomial.C_pow]
    rw [htwo, hsq]
    ring
  have hshift1 := hshift (2 * A) 1
  have hshift2 := hshift (A ^ 2) 2
  simp only [pow_one] at hshift1
  rw [hfamily, hquad, mul_add, mul_add,
    Polynomial.coeff_add, Polynomial.coeff_add, mul_one,
    hshift1, hshift2]
  simp [Polynomial.coeff_one_add_X_pow]

end MathlibPlus.Algebra.Claim14826
