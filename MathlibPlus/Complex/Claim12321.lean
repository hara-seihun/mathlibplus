import MathlibPlus.Basic

namespace MathlibPlus.Complex.Claim12321

/-- The displayed even quartic has no cubic coefficient and has an explicit
root with nonzero real and imaginary parts. -/
theorem traceNeutralOffAxisQuartic_claim12321 :
    let p : Polynomial ℂ :=
      Polynomial.X ^ 4 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.C 25
    p.coeff 3 = 0 ∧
      ∃ z : ℂ, p.eval z = 0 ∧ z.re ≠ 0 ∧ z.im ≠ 0 := by
  dsimp
  constructor
  · simp
  · refine ⟨1 + 2 * Complex.I, ?_, ?_, ?_⟩
    · simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C]
      apply Complex.ext <;> norm_num [pow_succ, Complex.mul_re, Complex.mul_im]
    · norm_num
    · norm_num

end MathlibPlus.Complex.Claim12321
