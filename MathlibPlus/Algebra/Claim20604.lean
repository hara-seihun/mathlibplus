import MathlibPlus.Basic

noncomputable section
open Polynomial

namespace MathlibPlus.Algebra.Claim20604

private lemma derivative_lehmerModTwo_ne_zero :
    derivative
        (X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : Polynomial (ZMod 2)) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 8) h
  rw [coeff_derivative] at hc
  simp [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_X_pow, Polynomial.coeff_X] at hc
  have hc' : (9 : ZMod 2) = 0 := by exact hc
  exact (by decide : (9 : ZMod 2) ≠ 0) hc'

private lemma derivative_paddingModTwo_eq_zero :
    derivative ((X + 1 : Polynomial (ZMod 2)) ^ 22) = 0 := by
  rw [derivative_pow]
  have htwo : (22 : ZMod 2) = 0 := by decide
  simp [htwo]

private lemma paddingModTwo_ne_zero :
    (X + 1 : Polynomial (ZMod 2)) ^ 22 ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 0) h
  rw [Polynomial.coeff_X_add_one_pow] at hc
  norm_num at hc

private lemma derivative_paddedLehmerModTwo_ne_zero :
    derivative
        ((X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : Polynomial (ZMod 2)) *
          (X + 1) ^ 22) ≠ 0 := by
  rw [derivative_mul, derivative_paddingModTwo_eq_zero, mul_zero, add_zero]
  exact mul_ne_zero derivative_lehmerModTwo_ne_zero paddingModTwo_ne_zero

/-- Claim 20604: the Lehmer polynomial padded by `(X + 1)^22` is not a square
in `F₂[X]`.  The integer polynomial is written out so that the reduction is
part of the statement rather than an implicit external convention. -/
theorem paddedLehmerPolynomial_not_square_mod_two_claim20604 :
    ¬ ∃ q : Polynomial (ZMod 2),
      q ^ 2 =
        Polynomial.map (Int.castRingHom (ZMod 2))
          ((X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : Polynomial ℤ) *
            (X + 1) ^ 22) := by
  rintro ⟨q, hq⟩
  have hmap :
      Polynomial.map (Int.castRingHom (ZMod 2))
          ((X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : Polynomial ℤ) *
            (X + 1) ^ 22) =
        (X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : Polynomial (ZMod 2)) *
          (X + 1) ^ 22 := by
    simp [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  rw [hmap] at hq
  have hzero :
      derivative
          ((X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 : Polynomial (ZMod 2)) *
            (X + 1) ^ 22) = 0 := by
    rw [← hq, derivative_sq]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp [htwo]
  exact derivative_paddedLehmerModTwo_ne_zero hzero

end MathlibPlus.Algebra.Claim20604
