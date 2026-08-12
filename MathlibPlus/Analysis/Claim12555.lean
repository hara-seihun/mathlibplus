import Mathlib

namespace MathlibPlus.Analysis.Claim12555

/--
The positive-weight derivative identity from admitted claim 12555.  The
notation `F' = (p - φ') A` is represented by the displayed pointwise
`HasDerivAt` hypothesis, and the implicit differentiability needed by the
derivative notation is made explicit.
-/
theorem positiveWeightDerivativeIdentity
    (p : ℝ) (φ F A : ℝ → ℝ) (x : ℝ)
    (hφ : HasDerivAt φ (deriv φ x) x)
    (hF : HasDerivAt F ((p - deriv φ x) * A x) x)
    (hA : HasDerivAt A (deriv A x) x) :
    deriv (fun y : ℝ => Real.exp (p * y - φ y) * (F y - A y)) x =
      Real.exp (p * x - φ x) *
        ((p - deriv φ x) * F x - deriv A x) := by
  have harg : HasDerivAt (fun y : ℝ => p * y - φ y)
      (p - deriv φ x) x := by
    have harg' := ((hasDerivAt_const x p).mul (hasDerivAt_id x)).sub hφ
    have heq : (fun y : ℝ => p * y - φ y) =ᶠ[nhds x]
        ((fun _ : ℝ => p) * id - φ) :=
      Filter.Eventually.of_forall (fun y => rfl)
    simpa using harg'.congr_of_eventuallyEq heq
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (p * y - φ y))
      (Real.exp (p * x - φ x) * (p - deriv φ x)) x := by
    have hexp' := (Real.hasDerivAt_exp (p * x - φ x)).comp x harg
    have heq : (fun y : ℝ => Real.exp (p * y - φ y)) =ᶠ[nhds x]
        (Real.exp ∘ (fun y : ℝ => p * y - φ y)) :=
      Filter.Eventually.of_forall (fun y => rfl)
    exact hexp'.congr_of_eventuallyEq heq
  have hprod : HasDerivAt
      (fun y : ℝ => Real.exp (p * y - φ y) * (F y - A y))
      (Real.exp (p * x - φ x) * (p - deriv φ x) * (F x - A x) +
        Real.exp (p * x - φ x) * ((p - deriv φ x) * A x - deriv A x)) x := by
    have hprod' := hexp.mul (hF.sub hA)
    have heq : (fun y : ℝ => Real.exp (p * y - φ y) * (F y - A y)) =ᶠ[nhds x]
        (fun y => Real.exp (p * y - φ y)) * (F - A) :=
      Filter.Eventually.of_forall (fun y => rfl)
    simpa using hprod'.congr_of_eventuallyEq heq
  calc
    deriv (fun y : ℝ => Real.exp (p * y - φ y) * (F y - A y)) x =
        Real.exp (p * x - φ x) * (p - deriv φ x) * (F x - A x) +
          Real.exp (p * x - φ x) * ((p - deriv φ x) * A x - deriv A x) := hprod.deriv
    _ = Real.exp (p * x - φ x) *
        ((p - deriv φ x) * F x - deriv A x) := by ring

end MathlibPlus.Analysis.Claim12555

