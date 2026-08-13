import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim9574

/--
The scalar polynomial fragment of claim 9574.  The positive-coefficient
quadratic has its two displayed reciprocal real roots, one of modulus greater
than one and the other of modulus less than one.

The source's weak-reversibility, deficiency-zero, and complex-balance claims
are not asserted here: their reaction-network carriers are not specified by
the source packet.
-/
theorem exactReciprocalRoots_claim9574 :
    let p : Polynomial ℝ := Polynomial.X ^ 2 + 3 * Polynomial.X + 1
    let rplus : ℝ := (-3 + Real.sqrt 5) / 2
    let rminus : ℝ := (-3 - Real.sqrt 5) / 2
    (∀ q : ℝ, p.eval q = 0 ↔ q = rplus ∨ q = rminus) ∧
      (∀ q : ℝ, 0 < q → 0 < p.eval q) ∧
      rplus * rminus = 1 ∧ |rplus| < 1 ∧ |rminus| > 1 := by
  dsimp
  have hs : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by
    norm_num
  have hlt : Real.sqrt (5 : ℝ) < 3 := by
    nlinarith
  have hrootplus :
      ((-3 + Real.sqrt 5) / 2 : ℝ) ^ 2 +
          3 * ((-3 + Real.sqrt 5) / 2) + 1 = 0 := by
    nlinarith
  have hrootminus :
      ((-3 - Real.sqrt 5) / 2 : ℝ) ^ 2 +
          3 * ((-3 - Real.sqrt 5) / 2) + 1 = 0 := by
    nlinarith
  constructor
  · intro q
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_pow]
    change q ^ 2 + 3 * q + 1 = 0 ↔ _
    constructor
    · intro hq
      have hfac :
          (q - ((-3 + Real.sqrt 5) / 2)) *
              (q - ((-3 - Real.sqrt 5) / 2)) = 0 := by
        nlinarith
      rcases mul_eq_zero.mp hfac with h | h
      · left
        nlinarith
      · right
        nlinarith
    · intro hq
      rcases hq with rfl | rfl
      · nlinarith [hrootplus]
      · nlinarith [hrootminus]
  · constructor
    · intro q hq
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_pow]
      change 0 < q ^ 2 + 3 * q + 1
      nlinarith [sq_nonneg q]
    · constructor
      · nlinarith
      · constructor
        · rw [abs_of_neg (by nlinarith :
            (-3 + Real.sqrt 5) / 2 < 0)]
          nlinarith
        · rw [abs_of_neg (by nlinarith :
            (-3 - Real.sqrt 5) / 2 < 0)]
          nlinarith

end MathlibPlus.Algebra.Claim9574
