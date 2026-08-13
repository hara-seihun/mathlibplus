import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim46090

/-- The displayed Hoggatt order-three Hankel polynomial has equal negative
`X^2` and `X^4` coefficients once `d ≥ 3`.  The source-specific identity
identifying this polynomial with the determinant is recorded at the ledger
alignment boundary because the source does not define `H_d` in the claim. -/
theorem hoggattHankelCoefficientFormula_claim46090 (d : ℕ) (hd : 3 ≤ d) :
    let q : Polynomial ℚ :=
      Polynomial.C ((d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12) *
        (Polynomial.X ^ 2 *
          (Polynomial.C (2 - (d : ℚ)) * Polynomial.X ^ 2 +
            Polynomial.C ((d : ℚ) ^ 2 + 3 * (d : ℚ) - 4) * Polynomial.X +
              Polynomial.C (2 - (d : ℚ))))
    q.coeff 2 = -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 ∧
      q.coeff 4 = -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 ∧
        q.coeff 2 < 0 ∧ q.coeff 4 < 0 := by
  dsimp
  have hd0 : 0 < (d : ℚ) := by
    exact_mod_cast (by omega : 0 < d)
  have hd1 : 0 < (d : ℚ) - 1 := by
    have h : (1 : ℚ) < (d : ℚ) := by
      exact_mod_cast (by omega : 1 < d)
    linarith
  have hd2 : 0 < (d : ℚ) - 2 := by
    have h : (2 : ℚ) < (d : ℚ) := by
      exact_mod_cast (by omega : 2 < d)
    linarith
  have h2 :
      (Polynomial.C ((d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12) *
          (Polynomial.X ^ 2 *
            (Polynomial.C (2 - (d : ℚ)) * Polynomial.X ^ 2 +
              Polynomial.C ((d : ℚ) ^ 2 + 3 * (d : ℚ) - 4) * Polynomial.X +
                Polynomial.C (2 - (d : ℚ))))).coeff 2 =
        (d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12 * (2 - (d : ℚ)) := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have h4 :
      (Polynomial.C ((d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12) *
          (Polynomial.X ^ 2 *
            (Polynomial.C (2 - (d : ℚ)) * Polynomial.X ^ 2 +
              Polynomial.C ((d : ℚ) ^ 2 + 3 * (d : ℚ) - 4) * Polynomial.X +
                Polynomial.C (2 - (d : ℚ))))).coeff 4 =
        (d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12 * (2 - (d : ℚ)) := by
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num
  have hformula :
      (Polynomial.C ((d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12) *
          (Polynomial.X ^ 2 *
            (Polynomial.C (2 - (d : ℚ)) * Polynomial.X ^ 2 +
              Polynomial.C ((d : ℚ) ^ 2 + 3 * (d : ℚ) - 4) * Polynomial.X +
                Polynomial.C (2 - (d : ℚ))))).coeff 2 =
        -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 := by
    calc
      _ = (d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12 * (2 - (d : ℚ)) := h2
      _ = -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 := by ring
  have hformula4 :
      (Polynomial.C ((d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12) *
          (Polynomial.X ^ 2 *
            (Polynomial.C (2 - (d : ℚ)) * Polynomial.X ^ 2 +
              Polynomial.C ((d : ℚ) ^ 2 + 3 * (d : ℚ) - 4) * Polynomial.X +
                Polynomial.C (2 - (d : ℚ))))).coeff 4 =
        -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 := by
    calc
      _ = (d : ℚ) * ((d : ℚ) - 1) ^ 2 / 12 * (2 - (d : ℚ)) := h4
      _ = -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 := by ring
  have hpos :
      0 < (d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 := by
    positivity
  have hneg :
      -(d : ℚ) * ((d : ℚ) - 1) ^ 2 * ((d : ℚ) - 2) / 12 < 0 := by
    nlinarith [hpos]
  exact ⟨hformula, hformula4, hformula ▸ hneg, hformula4 ▸ hneg⟩

end MathlibPlus.Algebra.Claim46090
