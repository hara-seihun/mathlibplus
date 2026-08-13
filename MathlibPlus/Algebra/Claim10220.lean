import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim10220

/-- If a formal mode product has constant and linear coefficients `1`, its
remainder after subtracting `1 + z` vanishes to quadratic order. -/
theorem quadraticModeProductVanishing
    {R : Type _} [Ring R] (P : Polynomial R)
    (h0 : P.coeff 0 = 1) (h1 : P.coeff 1 = 1) :
    (Polynomial.X : Polynomial R) ^ 2 ∣
      P - ((1 : Polynomial R) + (Polynomial.X : Polynomial R)) := by
  rw [Polynomial.X_pow_dvd_iff
    (f := P - ((1 : Polynomial R) + (Polynomial.X : Polynomial R))) (n := 2)]
  intro d hd
  interval_cases d
  · simp [Polynomial.coeff_sub, Polynomial.coeff_one, h0]
  · simp [Polynomial.coeff_sub, Polynomial.coeff_one, h1]

end MathlibPlus.Algebra.Claim10220
