import Mathlib

/-!
# The degree-eight order-five Karlin boundary witness

This is the explicit witness from admitted claim 859 (source record C-0056).
The determinant is the consecutive derivative determinant
`det [f^(i+j)(x)]` at the origin, not an arbitrary order-five minor.
-/

namespace MathlibPlus.Analysis

private lemma detFinFour {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 -
        A 1 2 * A 2 1 * A 3 3 + A 1 2 * A 2 3 * A 3 1 +
        A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 -
        A 1 2 * A 2 0 * A 3 3 + A 1 2 * A 2 3 * A 3 0 +
        A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 -
        A 1 1 * A 2 0 * A 3 3 + A 1 1 * A 2 3 * A 3 0 +
        A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 -
        A 1 1 * A 2 0 * A 3 2 + A 1 1 * A 2 2 * A 3 0 +
        A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp (discharger := decide) [Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The `n`th derivative of a polynomial evaluated at a real point. -/
private noncomputable def polyDerivEval
    (f : Polynomial ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.derivative^[n]) f).eval x

private lemma polyDerivEval_zero (f : Polynomial ℝ) (n : ℕ) :
    polyDerivEval f n 0 = (Nat.factorial n : ℝ) * f.coeff n := by
  rw [polyDerivEval, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative, Nat.zero_add, Nat.descFactorial_self]
  norm_num [nsmul_eq_mul]

/-- The centered order-five Karlin determinant. -/
private noncomputable def karlinH5 (f : Polynomial ℝ) (x : ℝ) : ℝ :=
  Matrix.det fun i j : Fin 5 => polyDerivEval f (i.1 + j.1) x

private noncomputable def degreeEightBoundaryPolynomial : Polynomial ℝ :=
  Polynomial.X ^ 3 * (Polynomial.X + 1) ^ 5

private theorem degreeEightBoundaryMatrix :
    (fun i j : Fin 5 =>
      polyDerivEval degreeEightBoundaryPolynomial (i.1 + j.1) 0) =
      (!![0, 0, 0, 6, 120;
          0, 0, 6, 120, 1200;
          0, 6, 120, 1200, 7200;
          6, 120, 1200, 7200, 25200;
          120, 1200, 7200, 25200, 40320] :
        Matrix (Fin 5) (Fin 5) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [polyDerivEval_zero, degreeEightBoundaryPolynomial,
      Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_add_one_pow, Nat.choose]

private theorem degreeEightBoundaryH5 :
    karlinH5 degreeEightBoundaryPolynomial 0 = -9953280 := by
  rw [karlinH5, degreeEightBoundaryMatrix, Matrix.det_succ_row_zero,
    Fin.sum_univ_five]
  simp (discharger := decide) [detFinFour, Fin.succAbove]
  norm_num

/--
The exact degree-eight boundary counterexample in claim 859: the polynomial is
positive-leading of degree eight, its complex roots are exactly `0` and `-1`,
and its order-five consecutive-derivative determinant at zero is the stated
negative integer.
-/
theorem degreeEightBoundaryCounterexample_claim859 :
    degreeEightBoundaryPolynomial.natDegree = 8 ∧
      0 < degreeEightBoundaryPolynomial.coeff 8 ∧
      (∀ z : ℂ,
        (Polynomial.map (algebraMap ℝ ℂ) degreeEightBoundaryPolynomial).IsRoot z
          ↔ z = 0 ∨ z = -1) ∧
      karlinH5 degreeEightBoundaryPolynomial 0 = -9953280 := by
  have hroots : ∀ z : ℂ,
      (Polynomial.map (algebraMap ℝ ℂ) degreeEightBoundaryPolynomial).IsRoot z
        ↔ z = 0 ∨ z = -1 := by
    intro z
    change (Polynomial.eval z
      (Polynomial.map (algebraMap ℝ ℂ) degreeEightBoundaryPolynomial) = 0) ↔ _
    rw [Polynomial.eval_map]
    simpa [degreeEightBoundaryPolynomial, eq_neg_iff_add_eq_zero]
  refine ⟨?_, ?_, hroots, degreeEightBoundaryH5⟩
  · have hX : (Polynomial.X : Polynomial ℝ) ≠ 0 := Polynomial.X_ne_zero
    have hXP : (Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := by
      simpa using (Polynomial.X_add_C_ne_zero (R := ℝ) 1)
    have hdeg : (Polynomial.X + 1 : Polynomial ℝ).natDegree = 1 := by
      simpa using (Polynomial.natDegree_X_add_C (R := ℝ) 1)
    rw [degreeEightBoundaryPolynomial,
      Polynomial.natDegree_mul (pow_ne_zero _ hX) (pow_ne_zero _ hXP)]
    rw [Polynomial.natDegree_pow (Polynomial.X + 1) 5, hdeg,
      Polynomial.natDegree_pow Polynomial.X 3, Polynomial.natDegree_X]
  · norm_num [degreeEightBoundaryPolynomial, Polynomial.coeff_X_pow_mul',
      Polynomial.coeff_X_add_one_pow, Nat.choose]

end MathlibPlus.Analysis
