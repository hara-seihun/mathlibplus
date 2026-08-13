import Mathlib

namespace MathlibPlus.Analysis

/--
Claim 17213: the square-root reparameterization of a logarithmic derivative.
The function called `H` in the packet is made explicit as
`H y = f (1/2 + sqrt y)`; the differentiability premise is the exact local
hypothesis needed for the displayed derivative identity.
-/
theorem xiLogDerivativeSqrt_claim17213 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hf : DifferentiableAt ℝ f ((1 / 2 : ℝ) + Real.sqrt x)) :
    Real.sqrt x *
          (deriv f ((1 / 2 : ℝ) + Real.sqrt x) /
            f ((1 / 2 : ℝ) + Real.sqrt x)) =
      2 * x * deriv (fun y : ℝ => f ((1 / 2 : ℝ) + Real.sqrt y)) x /
        f ((1 / 2 : ℝ) + Real.sqrt x) := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx.ne'
  have hshift : HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) + Real.sqrt y)
      (1 / (2 * Real.sqrt x)) x := by
    simpa using (hsqrt.const_add (1 / 2 : ℝ))
  have hcomp := hf.hasDerivAt.comp x hshift
  have hderiv :
      deriv (fun y : ℝ => f ((1 / 2 : ℝ) + Real.sqrt y)) x =
        deriv f ((1 / 2 : ℝ) + Real.sqrt x) * (1 / (2 * Real.sqrt x)) := by
    exact hcomp.deriv
  rw [hderiv]
  have hsqrt_ne : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  field_simp [hsqrt_ne]
  rw [Real.sq_sqrt (le_of_lt hx)]
  ring

end MathlibPlus.Analysis
