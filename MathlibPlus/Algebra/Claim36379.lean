import Mathlib

namespace MathlibPlus.Algebra.Claim36379

/-- Claim 36379: in the polynomial endpoint equation, equality of the two
nonzero powers forces equality of their natural exponents. -/
theorem equalTailFactorCounts_claim36379
    (H : Polynomial ℚ) (p q : ℕ)
    (hEq : (Polynomial.X : Polynomial ℚ) ^ 2 =
        (Polynomial.X : Polynomial ℚ) ^ q * H ∧
      (Polynomial.X : Polynomial ℚ) ^ 2 =
        (Polynomial.X : Polynomial ℚ) ^ p * H) :
    p = q := by
  have hX : (Polynomial.X : Polynomial ℚ) ≠ 0 := Polynomial.X_ne_zero
  have hX2 : (Polynomial.X : Polynomial ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 hX
  have hH : H ≠ 0 := by
    intro hH0
    rw [hH0] at hEq
    exact hX2 (by simpa using hEq.1)
  have hpow : (Polynomial.X : Polynomial ℚ) ^ q =
      (Polynomial.X : Polynomial ℚ) ^ p := by
    apply (mul_right_cancel₀ hH)
    exact hEq.1.symm.trans hEq.2
  have hdegree := congrArg Polynomial.natDegree hpow
  simpa using hdegree.symm

end MathlibPlus.Algebra.Claim36379
