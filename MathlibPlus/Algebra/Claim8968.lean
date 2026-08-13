import Mathlib

open Polynomial
open scoped BigOperators

namespace MathlibPlus.Algebra.Claim8968

/-- The constant-term determinant identity for a monic polynomial whose lifted
zeros are listed with multiplicity. -/
theorem determinant_from_lifted_zeros
    {R : Type*} [CommRing R] (k : ℕ) (p : R[X]) (y : Fin k → R)
    (_hmonic : p.Monic) (_hdegree : p.natDegree = k)
    (hfactor : p = ∏ j : Fin k, (X - C ((y j) ^ 2))) :
    (-1 : R) ^ k * p.eval 0 = ∏ j : Fin k, (y j) ^ 2 := by
  rw [hfactor, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    zero_sub]
  rw [Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_fin]
  calc
    (-1 : R) ^ k * ((-1 : R) ^ k * ∏ x : Fin k, y x ^ 2) =
        ((-1 : R) ^ k * (-1 : R) ^ k) * ∏ x : Fin k, y x ^ 2 := by
          rw [mul_assoc]
    _ = ∏ x : Fin k, y x ^ 2 := by
      rw [← pow_add]
      have h_even : k + k = 2 * k := by omega
      rw [h_even, pow_mul]
      simp

end MathlibPlus.Algebra.Claim8968
