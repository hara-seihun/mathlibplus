import Mathlib

namespace MathlibPlus.Algebra.FactorialTransform

open scoped BigOperators

/-- The multi-index factorial appearing in the coefficientwise factorial transform.
For `a : σ →₀ ℕ`, this is the product of the factorials of its exponents. -/
noncomputable def factorialWeight {σ : Type*} [DecidableEq σ] (a : σ →₀ ℕ) : ℚ :=
  ∏ i ∈ a.support, (a i).factorial

/-- Divide the coefficient of each monomial by its multi-index factorial. -/
noncomputable def factorialTransform {σ : Type*} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  Finsupp.sum (AddMonoidAlgebra.coeff p)
    fun a c => MvPolynomial.C (c / factorialWeight a) * MvPolynomial.monomial a 1

private lemma factorialTransform_add {σ : Type*} [DecidableEq σ]
    (p q : MvPolynomial σ ℚ) :
    factorialTransform (p + q) = factorialTransform p + factorialTransform q := by
  unfold factorialTransform
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index'
  · intro a
    simp
  · intro a b₁ b₂
    rw [add_div, map_add]
    ring

/-- The transform acts on one monomial by the displayed factorial division. -/
theorem factorialTransform_monomial {σ : Type*} [DecidableEq σ]
    (a : σ →₀ ℕ) (c : ℚ) :
    factorialTransform (MvPolynomial.monomial a c) =
      MvPolynomial.C (c / factorialWeight a) * MvPolynomial.monomial a 1 := by
  simp [factorialTransform]

/-- Finite coefficient form of the factorial-transform identity (claim 25376). -/
theorem factorialTransform_sum_claim25376 {σ : Type*} [DecidableEq σ]
    (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ℚ) :
    factorialTransform (∑ a ∈ s, MvPolynomial.monomial a (c a)) =
      ∑ a ∈ s,
        MvPolynomial.C (c a / factorialWeight a) * MvPolynomial.monomial a 1 := by
  induction s using Finset.induction_on with
  | empty => simp [factorialTransform]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, factorialTransform_add, ih]
      simp [factorialTransform]
      rw [Finset.sum_insert ha]

end MathlibPlus.Algebra.FactorialTransform
