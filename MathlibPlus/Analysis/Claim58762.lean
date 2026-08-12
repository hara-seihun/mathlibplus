import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 58762: the Lagrange cardinal and Lebesgue formulas for a finite
prefix of pairwise-distinct real nodes. -/
theorem lagrangeLebesgue_formula_claim58762
    (n : ℕ) (t : Fin n → ℝ) (_ht : Function.Injective t) :
    (∀ (i : Fin n) (x : ℝ),
      (Lagrange.basis (Finset.univ : Finset (Fin n)) t i).eval x =
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          (x - t j) / (t i - t j)) ∧
    (∀ x : ℝ,
      (∑ i : Fin n,
        |(Lagrange.basis (Finset.univ : Finset (Fin n)) t i).eval x|) =
        ∑ i : Fin n,
          |∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
            (x - t j) / (t i - t j)|) := by
  constructor
  · intro i x
    rw [Lagrange.basis, Polynomial.eval_prod]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    rw [div_eq_mul_inv]
    ring
  · intro x
    apply Finset.sum_congr rfl
    intro i hi
    rw [Lagrange.basis, Polynomial.eval_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    rw [div_eq_mul_inv]
    ring

end

end MathlibPlus.Analysis
