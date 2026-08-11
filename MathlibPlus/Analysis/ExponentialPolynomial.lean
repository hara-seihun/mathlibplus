import Mathlib

/-!
# Exponential times polynomial differentiation

Formalization of admitted claim 4462.
-/

namespace MathlibPlus.Analysis.ExponentialPolynomial

/--
Claim 4462: for every real polynomial `p`,
`d/dx [exp (-x) * p(x)] = exp (-x) * (p'(x) - p(x))`.
-/
theorem exponentialNegMulPolynomial_deriv (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun x : ℝ => Real.exp (-x) * p.eval x) x =
      Real.exp (-x) * (p.derivative.eval x - p.eval x) := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
  have hm := (he.mul (p.hasDerivAt x)).deriv
  change deriv (fun y : ℝ => Real.exp (-y) * p.eval y) x =
    -Real.exp (-x) * p.eval x + Real.exp (-x) * p.derivative.eval x at hm
  calc
    deriv (fun y : ℝ => Real.exp (-y) * p.eval y) x =
        -Real.exp (-x) * p.eval x + Real.exp (-x) * p.derivative.eval x := hm
    _ = Real.exp (-x) * (p.derivative.eval x - p.eval x) := by ring

end MathlibPlus.Analysis.ExponentialPolynomial
