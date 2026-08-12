import MathlibPlus.Basic

noncomputable section

namespace MathlibPlus.Analysis.Claim4455

/-- The exponential conjugate of differentiation, evaluated on a polynomial.
The source's phrase "exponential conjugation" is represented as
`exp x · D (exp (-·) · p)` on the real line. -/
def conjugatedDerivative (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  Real.exp x * deriv (fun y : ℝ => Real.exp (-y) * p.eval y) x

/-- Claim 4455: exponential conjugation turns differentiation of a polynomial
into the polynomial operator `p ↦ p' - p`. -/
theorem conjugated_derivative_eq (p : Polynomial ℝ) (x : ℝ) :
    conjugatedDerivative p x = p.derivative.eval x - p.eval x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
  have hpoly : HasDerivAt (fun y : ℝ => p.eval y) (p.derivative.eval x) x := by
    simpa using p.hasDerivAt x
  have hmul := hexp.mul hpoly
  rw [conjugatedDerivative]
  have hfun : (fun y : ℝ => Real.exp (-y)) * (fun y => p.eval y) =
      (fun y : ℝ => Real.exp (-y) * p.eval y) := by
    funext y
    rfl
  have hderiv0 := hmul.deriv
  rw [hfun] at hderiv0
  have hderiv : deriv (fun y : ℝ => Real.exp (-y) * p.eval y) x =
      -Real.exp (-x) * p.eval x + Real.exp (-x) * p.derivative.eval x := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hderiv0
  rw [hderiv]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    Real.exp x * (-Real.exp (-x) * p.eval x + Real.exp (-x) * p.derivative.eval x) =
        -(Real.exp x * Real.exp (-x)) * p.eval x +
          (Real.exp x * Real.exp (-x)) * p.derivative.eval x := by ring
    _ = p.derivative.eval x - p.eval x := by rw [hprod]; ring

end MathlibPlus.Analysis.Claim4455
