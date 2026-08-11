import Mathlib

/-!
# Beta derivative of the shell profile

The exact differential identity extracted from admitted claim 12907 is recorded
for the real-valued shell profile.  The source's additional phrase “sign-
oscillating regime” is not a defined mathematical predicate in this file.
-/

namespace MathlibPlus.Analysis.ShellBetaDerivative

/-- The shell profile from claim 12907. -/
noncomputable def shellProfile (α β t : ℝ) : ℝ :=
  Real.cosh (α * t) * Real.exp (-β * Real.cosh (2 * t))

/-- Differentiating in `β` is multiplication by `-cosh (2*t)`; after the
source's normalization by `-2`, this is multiplication by `2*cosh (2*t)`. -/
theorem negTwoBetaDerivative (α β t : ℝ) :
    -2 * deriv (fun b : ℝ => shellProfile α b t) β =
      2 * Real.cosh (2 * t) * shellProfile α β t := by
  have hinner : HasDerivAt (fun b : ℝ => -b * Real.cosh (2 * t))
      (-Real.cosh (2 * t)) β := by
    simpa [id_eq] using (hasDerivAt_id β).mul_const (-Real.cosh (2 * t))
  have hexp : HasDerivAt (fun b : ℝ => Real.exp (-b * Real.cosh (2 * t)))
      (Real.exp (-β * Real.cosh (2 * t)) * (-Real.cosh (2 * t))) β := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-β * Real.cosh (2 * t))).comp β hinner
  have hconst : HasDerivAt (fun _ : ℝ => Real.cosh (α * t)) 0 β :=
    hasDerivAt_const β (Real.cosh (α * t))
  have hprod := hconst.mul hexp
  have hderiv : HasDerivAt (fun b : ℝ => shellProfile α b t)
      (-Real.cosh (α * t) * Real.cosh (2 * t) *
        Real.exp (-β * Real.cosh (2 * t))) β := by
    convert hprod using 1 <;> try rfl
    simp only [zero_mul, zero_add]
    ring
  rw [hderiv.deriv]
  simp [shellProfile]
  ring

end MathlibPlus.Analysis.ShellBetaDerivative
