import Mathlib

namespace MathlibPlus.Analysis

/--
Claim 11753.  The displayed cubic Jensen polynomial factors into two negative
real linear factors, while the displayed order-three Toeplitz minor is
negative.  The polynomial and matrix are written over `ℝ` so the root and
minor assertions are exact rather than numerical.
-/
theorem rationalHyperbolicCounterfeit_claim11753 :
    let P : Polynomial ℝ := 1 + 4 * Polynomial.X + 5 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3
    let M : Matrix (Fin 3) (Fin 3) ℝ :=
      !![(4 / 3 : ℝ), 5 / 3, 2;
         1, 4 / 3, 5 / 3;
         0, 1, 4 / 3]
    P = (1 + Polynomial.X) ^ 2 * (1 + 2 * Polynomial.X) ∧
      (∀ z : ℝ, P.eval z = 0 → z = -1 ∨ z = -(1 / 2 : ℝ)) ∧
      Matrix.det M = -(2 : ℝ) / 27 := by
  dsimp
  have hfactor :
      (1 + 4 * Polynomial.X + 5 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 : Polynomial ℝ) =
        (1 + Polynomial.X) ^ 2 * (1 + 2 * Polynomial.X) := by
    ring
  refine ⟨hfactor, ?_, ?_⟩
  · intro z hz
    rw [hfactor] at hz
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_ofNat] at hz
    rcases mul_eq_zero.mp hz with hleft | hright
    · have hlinear : 1 + z = 0 := by
        nlinarith [sq_nonneg (1 + z)]
      left
      linarith
    · right
      linarith
  · simp (discharger := decide) [Matrix.det_fin_three]
    norm_num

end MathlibPlus.Analysis
