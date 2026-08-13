import Mathlib
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

namespace MathlibPlus.Combinatorics.Claim24846

open scoped BigOperators
open Polynomial

noncomputable section

private abbrev Coeff := MvPolynomial ℕ ℤ
private abbrev MarkerPoly := Polynomial Coeff
private def markerVariable : MarkerPoly := Polynomial.X

private noncomputable def markerExpansion
    (polynomial : MarkerPoly) : Coeff :=
  ∑ degree ∈ polynomial.support,
    MvPolynomial.X degree * polynomial.coeff degree

private theorem markerExpansion_mul_C
    (polynomial : MarkerPoly) (coefficient : Coeff) :
    markerExpansion (polynomial * Polynomial.C coefficient) =
      markerExpansion polynomial * coefficient := by
  classical
  let product := polynomial * Polynomial.C coefficient
  have support_subset : product.support ⊆ polynomial.support := by
    intro degree degree_mem
    by_contra degree_not_mem
    have coefficient_zero : polynomial.coeff degree = 0 :=
      Polynomial.notMem_support_iff.mp degree_not_mem
    have product_coefficient_zero : product.coeff degree = 0 := by
      dsimp [product]
      rw [Polynomial.coeff_mul_C, coefficient_zero, zero_mul]
    exact (Polynomial.mem_support_iff.mp degree_mem) product_coefficient_zero
  have missing_terms_zero :
      ∀ degree ∈ polynomial.support, degree ∉ product.support →
        MvPolynomial.X degree * product.coeff degree = 0 := by
    intro degree degree_mem degree_not_mem
    have product_coefficient_zero : product.coeff degree = 0 :=
      Polynomial.notMem_support_iff.mp degree_not_mem
    simp [product_coefficient_zero]
  unfold markerExpansion
  change
    (∑ degree ∈ product.support,
        MvPolynomial.X degree * product.coeff degree) =
      (∑ degree ∈ polynomial.support,
        MvPolynomial.X degree * polynomial.coeff degree) * coefficient
  rw [Finset.sum_subset support_subset missing_terms_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro degree degree_mem
  simp only [product, Polynomial.coeff_mul_C]
  ring

private theorem markerExpansion_add
    (left right : MarkerPoly) :
    markerExpansion (left + right) =
      markerExpansion left + markerExpansion right := by
  classical
  let union := left.support ∪ right.support
  have support_subset : (left + right).support ⊆ union := by
    intro degree degree_mem
    by_contra degree_not_mem
    have left_zero : left.coeff degree = 0 := by
      apply Polynomial.notMem_support_iff.mp
      intro left_mem
      exact degree_not_mem (Finset.mem_union_left _ left_mem)
    have right_zero : right.coeff degree = 0 := by
      apply Polynomial.notMem_support_iff.mp
      intro right_mem
      exact degree_not_mem (Finset.mem_union_right _ right_mem)
    exact (Polynomial.mem_support_iff.mp degree_mem) (by
      simp [Polynomial.coeff_add, left_zero, right_zero])
  have missing_terms_zero :
      ∀ degree ∈ union, degree ∉ (left + right).support →
        MvPolynomial.X degree * (left + right).coeff degree = 0 := by
    intro degree degree_mem degree_not_mem
    have coefficient_zero : (left + right).coeff degree = 0 :=
      Polynomial.notMem_support_iff.mp degree_not_mem
    simp [coefficient_zero]
  have left_missing_zero :
      ∀ degree ∈ union, degree ∉ left.support →
        MvPolynomial.X degree * left.coeff degree = 0 := by
    intro degree degree_mem degree_not_mem
    have coefficient_zero : left.coeff degree = 0 :=
      Polynomial.notMem_support_iff.mp degree_not_mem
    simp [coefficient_zero]
  have right_missing_zero :
      ∀ degree ∈ union, degree ∉ right.support →
        MvPolynomial.X degree * right.coeff degree = 0 := by
    intro degree degree_mem degree_not_mem
    have coefficient_zero : right.coeff degree = 0 :=
      Polynomial.notMem_support_iff.mp degree_not_mem
    simp [coefficient_zero]
  unfold markerExpansion
  change
    (∑ degree ∈ (left + right).support,
        MvPolynomial.X degree * (left + right).coeff degree) =
      (∑ degree ∈ left.support,
        MvPolynomial.X degree * left.coeff degree) +
        ∑ degree ∈ right.support,
          MvPolynomial.X degree * right.coeff degree
  rw [Finset.sum_subset support_subset missing_terms_zero]
  calc
    (∑ degree ∈ union,
        MvPolynomial.X degree * (left + right).coeff degree) =
        (∑ degree ∈ union,
          MvPolynomial.X degree * left.coeff degree) +
          ∑ degree ∈ union,
            MvPolynomial.X degree * right.coeff degree := by
          simp_rw [Polynomial.coeff_add, mul_add]
          rw [Finset.sum_add_distrib]
    _ = (∑ degree ∈ left.support,
          MvPolynomial.X degree * left.coeff degree) +
          ∑ degree ∈ right.support,
            MvPolynomial.X degree * right.coeff degree := by
          rw [Finset.sum_subset (Finset.subset_union_left) left_missing_zero,
            Finset.sum_subset (Finset.subset_union_right) right_missing_zero]

private theorem markerExpansion_sub
    (left right : MarkerPoly) :
    markerExpansion (left - right) =
      markerExpansion left - markerExpansion right := by
  rw [sub_eq_add_neg, markerExpansion_add]
  rw [show -right = right * Polynomial.C (-1 : Coeff) by
    ext degree
    rw [Polynomial.coeff_neg, Polynomial.coeff_mul_C]
    simp]
  rw [markerExpansion_mul_C]
  ring

private theorem markerExpansion_X_pow_mul_C
    (exponent : ℕ) (coefficient : Coeff) :
    markerExpansion
        (markerVariable ^ exponent * Polynomial.C coefficient) =
      MvPolynomial.X exponent * coefficient := by
  rw [markerExpansion_mul_C]
  congr 1
  classical
  simp [markerExpansion, markerVariable]

private def markerDerivative (polynomial : MarkerPoly) : Coeff :=
  MvPolynomial.pderiv 1 (markerExpansion (markerVariable * polynomial))

private theorem markerDerivative_add
    (left right : MarkerPoly) :
    markerDerivative (left + right) =
      markerDerivative left + markerDerivative right := by
  unfold markerDerivative
  rw [mul_add, markerExpansion_add, map_add]

private theorem markerDerivative_sub
    (left right : MarkerPoly) :
    markerDerivative (left - right) =
      markerDerivative left - markerDerivative right := by
  unfold markerDerivative
  rw [mul_sub, markerExpansion_sub, map_sub]

private theorem markerDerivative_of_X_pow_mul_C_of_ne
    (exponent : ℕ) (exponent_ne_zero : exponent ≠ 0)
    (coefficient : Coeff) :
    markerDerivative
        (markerVariable ^ exponent * Polynomial.C coefficient) =
      MvPolynomial.X (exponent + 1) *
        MvPolynomial.pderiv 1 coefficient := by
  unfold markerDerivative
  rw [show markerVariable *
        (markerVariable ^ exponent * Polynomial.C coefficient) =
      markerVariable ^ (exponent + 1) * Polynomial.C coefficient by
        rw [show markerVariable *
              (markerVariable ^ exponent * Polynomial.C coefficient) =
            (markerVariable ^ exponent * markerVariable) *
              Polynomial.C coefficient by ring]
        rw [← pow_succ]]
  rw [markerExpansion_X_pow_mul_C]
  rw [MvPolynomial.pderiv_mul]
  have variable_ne_one : exponent + 1 ≠ 1 := by omega
  rw [MvPolynomial.pderiv_X_of_ne variable_ne_one]
  simp

private theorem markerDerivative_of_X_mul_C
    (coefficient : Coeff) :
    markerDerivative
        (markerVariable * Polynomial.C coefficient) =
      MvPolynomial.X 2 * MvPolynomial.pderiv 1 coefficient := by
  simpa only [pow_one] using
    (markerDerivative_of_X_pow_mul_C_of_ne 1 (by norm_num) coefficient)

private def eAxis : MarkerPoly :=
  markerVariable ^ 2 * Polynomial.C
      (MvPolynomial.X 3 * MvPolynomial.X 1 ^ 2)
    - markerVariable * Polynomial.C
      (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)

private def singletonPad (exponent : ℕ) (polynomial : MarkerPoly) : MarkerPoly :=
  Polynomial.C (MvPolynomial.X 1 ^ exponent) * polynomial

theorem imageOfE4Axis_claim24846
    (u : ℕ) :
    markerDerivative (singletonPad u eAxis) =
      (u + 2 : ℤ) •
          (MvPolynomial.X 3 ^ 2 * MvPolynomial.X 1 ^ (u + 1))
        - (u + 1 : ℤ) •
          (MvPolynomial.X 3 * MvPolynomial.X 2 ^ 2 *
            MvPolynomial.X 1 ^ u) := by
  unfold singletonPad eAxis
  rw [show Polynomial.C (MvPolynomial.X 1 ^ u) *
        (markerVariable ^ 2 * Polynomial.C
            (MvPolynomial.X 3 * MvPolynomial.X 1 ^ 2)
          - markerVariable * Polynomial.C
              (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)) =
      markerVariable ^ 2 * Polynomial.C
          (MvPolynomial.X 1 ^ u *
            (MvPolynomial.X 3 * MvPolynomial.X 1 ^ 2))
        - markerVariable * Polynomial.C
            (MvPolynomial.X 1 ^ u *
              (MvPolynomial.X 3 * MvPolynomial.X 2 * MvPolynomial.X 1)) by
        simp only [mul_sub, mul_assoc, mul_comm, mul_left_comm,
          ← Polynomial.coeff_C_mul, ← Polynomial.C_mul]]
  rw [markerDerivative_sub,
    markerDerivative_of_X_pow_mul_C_of_ne 2 (by norm_num),
    markerDerivative_of_X_mul_C]
  simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]
  cases u with
  | zero => ring
  | succ u =>
      simp only [Nat.succ_sub_one]
      ring

end
end MathlibPlus.Combinatorics.Claim24846
