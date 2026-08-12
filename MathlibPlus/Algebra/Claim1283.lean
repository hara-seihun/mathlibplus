import Mathlib

namespace MathlibPlus.Algebra.Claim1283

/-- The explicit positive quadratic in claim 1283 has a negative linear
coefficient, so pointwise positivity alone does not imply coefficientwise
positivity. -/
theorem positiveQuadraticNegativeCoefficient_claim1283 :
    let q : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.X + 1
    (∀ b : ℝ, 0 < q.eval b) ∧
      Polynomial.coeff q 1 = (-1 : ℝ) ∧
      ¬ (∀ n : ℕ, 0 ≤ Polynomial.coeff q n) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro b
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    nlinarith [sq_nonneg (b - (1 / 2 : ℝ))]
  · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one]
  · intro h
    have h1 := h 1
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_X_pow, Polynomial.coeff_one] at h1

end MathlibPlus.Algebra.Claim1283
