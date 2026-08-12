import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim11236

open Polynomial

/-- The `m = 1` quartic becomes `Y^2 + 1` after the substitution `Y = z^2`. -/
theorem squareVariableShadow_discriminant_claim11236 :
    ((X ^ 4 + 1 : Polynomial ℤ) = (X ^ 2 : Polynomial ℤ) ^ 2 + 1) ∧
      Polynomial.discr (X ^ 2 + 1 : Polynomial ℤ) = -4 := by
  constructor
  · ring
  · have hne : (X ^ 2 + 1 : Polynomial ℤ) ≠ 0 := by
      intro h
      have hc := congrArg (fun p : Polynomial ℤ => p.coeff 2) h
      norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc
    have hdeg : (X ^ 2 + 1 : Polynomial ℤ).degree = 2 := by
      rw [Polynomial.degree_eq_natDegree hne]
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
      · simp
      · simp
    rw [Polynomial.discr_of_degree_eq_two hdeg]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one]

end MathlibPlus.Algebra.Claim11236
