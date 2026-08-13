import Mathlib

namespace MathlibPlus.Analysis.Claim17580

/-!
Formalization of admitted claim 17580.  The displayed `P` is represented by
`P z = R z * F z * F (-z)`.  The phrase "wherever all factors are nonzero"
is made pointwise: the three factors are nonzero at `x`, and the derivatives
are required at the points where they are used.
-/

/-- Pointwise logarithmic-derivative split for
`P z = R z * F z * F (-z)`. -/
theorem logarithmicDerivativeSplit_claim17580
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    (R F : 𝕜 → 𝕜) (x : 𝕜)
    (hR : DifferentiableAt 𝕜 R x)
    (hF : DifferentiableAt 𝕜 F x)
    (hFneg : DifferentiableAt 𝕜 F (-x))
    (hR0 : R x ≠ 0) (hF0 : F x ≠ 0) (hFneg0 : F (-x) ≠ 0) :
    deriv (fun z => R z * F z * F (-z)) x /
        (R x * F x * F (-x)) =
      deriv R x / R x + deriv F x / F x - deriv F (-x) / F (-x) := by
  have hR' : HasDerivAt R (deriv R x) x := hR.hasDerivAt
  have hF' : HasDerivAt F (deriv F x) x := hF.hasDerivAt
  have hFneg' : HasDerivAt F (deriv F (-x)) (-x) := hFneg.hasDerivAt
  have hFcomp0 := hFneg'.comp x (hasDerivAt_neg x)
  have hFcomp' : HasDerivAt (fun z => F (-z)) (-deriv F (-x)) x := by
    have h := hFcomp0.congr_of_eventuallyEq
      (f₁ := fun z => F (-z))
      (Filter.Eventually.of_forall (fun z => by
        simp only [Function.comp_apply]))
    simpa only [Function.comp_apply, mul_neg, mul_one] using h
  have hprod0 := (hR'.mul hF').mul hFcomp'
  have hprod : HasDerivAt (fun z => R z * F z * F (-z))
      ((deriv R x * F x + R x * deriv F x) * F (-x) -
        (R x * F x) * deriv F (-x)) x := by
    have h := hprod0.congr_of_eventuallyEq
      (f₁ := fun z => R z * F z * F (-z))
      (Filter.Eventually.of_forall (fun z => by
        simp only [Pi.mul_apply]))
    simpa [Pi.mul_apply, sub_eq_add_neg, mul_assoc] using h
  rw [hprod.deriv]
  field_simp [hR0, hF0, hFneg0]

end MathlibPlus.Analysis.Claim17580
