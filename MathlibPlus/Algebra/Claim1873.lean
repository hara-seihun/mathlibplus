import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim1873

/-!
The admitted claim also describes a packet-specific near-hook mutation, an exact
principal quotient, and a shifted coordinate.  Those objects are not defined in
the claim text.  This file formalizes its explicit, self-contained witness: the
quadratic `b^2 - b + 1` is positive on `ℝ`, while its linear coefficient is `-1`.
-/

/-- The explicit quadratic witness in admitted claim 1873 is positive on the real
line, while its linear coefficient is negative. -/
theorem pointwisePositiveQuadratic :
    let p : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.X + 1
    (∀ b : ℝ, 0 < p.eval b) ∧ p.coeff 1 = -1 := by
  dsimp
  constructor
  · intro b
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_one]
    nlinarith [sq_nonneg (b - (1 / 2 : ℝ))]
  · norm_num [Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]

end MathlibPlus.Algebra.Claim1873
