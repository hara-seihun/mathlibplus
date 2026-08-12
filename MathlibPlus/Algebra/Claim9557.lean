import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim9557

/--
Claim 9557.  For the explicit witness polynomial
`g(u) = u^2 - 3u + 1`, the two real roots are the reciprocal pair
`(3 ± √5) / 2`; in particular both roots are positive and off the unit
circle.  The source writes the roots over `ℚ`; this theorem makes the real
root domain used by the displayed square-root formulas explicit.
-/
theorem exactReciprocalRoots :
    let g : Polynomial ℝ := Polynomial.X ^ 2 - 3 * Polynomial.X + 1
    let uPlus : ℝ := (3 + Real.sqrt 5) / 2
    let uMinus : ℝ := (3 - Real.sqrt 5) / 2
    (∀ u : ℝ, g.eval u = 0 ↔ u = uPlus ∨ u = uMinus) ∧
      0 < uMinus ∧ 0 < uPlus ∧ uMinus ≠ uPlus ∧
      uPlus * uMinus = 1 ∧ uPlus > 1 ∧ uMinus < 1 := by
  dsimp
  have hs : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by
    norm_num
  have hlt : Real.sqrt (5 : ℝ) < 3 := by
    nlinarith
  have hrootplus :
      ((3 + Real.sqrt 5) / 2 : ℝ) ^ 2 -
          3 * ((3 + Real.sqrt 5) / 2) + 1 = 0 := by
    nlinarith
  have hrootminus :
      ((3 - Real.sqrt 5) / 2 : ℝ) ^ 2 -
          3 * ((3 - Real.sqrt 5) / 2) + 1 = 0 := by
    nlinarith
  constructor
  · intro u
    simp [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X]
    change u ^ 2 - 3 * u + 1 = 0 ↔ _
    constructor
    · intro hu
      have hfac : (u - ((3 + Real.sqrt 5) / 2)) *
          (u - ((3 - Real.sqrt 5) / 2)) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfac with h | h
      · left
        nlinarith
      · right
        nlinarith
    · intro hu
      rcases hu with rfl | rfl
      · nlinarith [hrootplus]
      · nlinarith [hrootminus]
  · constructor
    · nlinarith
    · constructor
      · nlinarith
      · constructor
        · nlinarith
        · constructor
          · field_simp
            nlinarith
          · constructor <;> nlinarith

end MathlibPlus.Algebra.Claim9557
