import MathlibPlus.Algebra.LaurentNullKernelToy

open scoped LaurentPolynomial

namespace MathlibPlus.Algebra.Claim50754

/--
The exact Laurent-polynomial toy from admitted claim 50754.  `q_inv` is the
formal inverse generator `T (-1)`; the accompanying final conjunct checks
that it is inverse to `q`.  The integer polynomial records the claimed
positive integral coefficient vector separately from its Laurent realization.
-/
theorem reciprocalLaurentPolynomialClaim :
    let q : ℚ[T;T⁻¹] := LaurentPolynomial.T 1
    let q_inv : ℚ[T;T⁻¹] := LaurentPolynomial.T (-1)
    let P_in : ℚ[T;T⁻¹] := (5 * q + 4) * (4 * q + 5)
    let P_out : ℚ[T;T⁻¹] := (2 * q + 1) * (q + 2)
    let P : ℚ[T;T⁻¹] := P_in * P_out
    let Ppoly : Polynomial ℤ :=
      40 + 182 * Polynomial.X + 285 * Polynomial.X ^ 2 +
        182 * Polynomial.X ^ 3 + 40 * Polynomial.X ^ 4
    P_in = 20 * q ^ 2 + 41 * q + 20 ∧
      P_out = 2 * q ^ 2 + 5 * q + 2 ∧
      P = 40 * q ^ 4 + 182 * q ^ 3 + 285 * q ^ 2 + 182 * q + 40 ∧
      (∀ i : Fin 5, 0 < Ppoly.coeff i.1) ∧
      q ^ 4 *
          (40 * q_inv ^ 4 + 182 * q_inv ^ 3 + 285 * q_inv ^ 2 +
            182 * q_inv + 40) = P := by
  have expand_in : ∀ q : ℚ[T;T⁻¹],
      (5 * q + 4) * (4 * q + 5) = 20 * q ^ 2 + 41 * q + 20 := by
    intro q
    ring
  have expand_out : ∀ q : ℚ[T;T⁻¹],
      (2 * q + 1) * (q + 2) = 2 * q ^ 2 + 5 * q + 2 := by
    intro q
    ring
  have expand_product : ∀ q : ℚ[T;T⁻¹],
      ((5 * q + 4) * (4 * q + 5)) * ((2 * q + 1) * (q + 2)) =
        40 * q ^ 4 + 182 * q ^ 3 + 285 * q ^ 2 + 182 * q + 40 := by
    intro q
    ring
  have reciprocal : ∀ (q q_inv : ℚ[T;T⁻¹]), q * q_inv = 1 →
      q ^ 4 *
          (40 * q_inv ^ 4 + 182 * q_inv ^ 3 + 285 * q_inv ^ 2 +
            182 * q_inv + 40) =
        40 * q ^ 4 + 182 * q ^ 3 + 285 * q ^ 2 + 182 * q + 40 := by
    intro q q_inv h
    have h1 : q ^ 4 * q_inv = q ^ 3 := by
      calc
        q ^ 4 * q_inv = q ^ 3 * (q * q_inv) := by ring
        _ = q ^ 3 := by rw [h, mul_one]
    have h2 : q ^ 4 * q_inv ^ 2 = q ^ 2 := by
      calc
        q ^ 4 * q_inv ^ 2 = q ^ 2 * (q * q_inv) ^ 2 := by ring
        _ = q ^ 2 := by rw [h, one_pow, mul_one]
    have h3 : q ^ 4 * q_inv ^ 3 = q := by
      calc
        q ^ 4 * q_inv ^ 3 = q * (q * q_inv) ^ 3 := by ring
        _ = q := by rw [h, one_pow, mul_one]
    have h4 : q ^ 4 * q_inv ^ 4 = 1 := by
      calc
        q ^ 4 * q_inv ^ 4 = (q * q_inv) ^ 4 := by ring
        _ = 1 := by rw [h, one_pow]
    ring_nf
    rw [h1, h2, h3, h4]
    ac_rfl
  dsimp
  constructor
  · exact expand_in _
  constructor
  · exact expand_out _
  constructor
  · exact expand_product _
  constructor
  · intro i
    fin_cases i <;>
      norm_num [Polynomial.coeff_add, Polynomial.coeff_mul,
        Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul]
  · rw [expand_product]
    apply reciprocal
    rw [← LaurentPolynomial.T_add]
    norm_num

end MathlibPlus.Algebra.Claim50754
