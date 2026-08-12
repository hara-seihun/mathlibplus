import Mathlib

namespace MathlibPlus.Analysis.Claim21423

open Filter

/-- The inverse-phase identity from claim 21423.

The source's smooth increasing phase is represented by the strictly monotone
`q`, the continuous inverse branch `X`, and the three derivative profiles
`q'`, `q''`, and `q'''`.  The right-inverse equation and nonvanishing first
profile are kept explicit because they are exactly what the inverse-function
calculation uses. -/
theorem inversePhase_secondDerivative_claim21423
    (q X q' q'' q''' : ℝ → ℝ)
    (hXcont : Continuous X)
    (_hqmono : StrictMono q)
    (hleft : ∀ y, q (X y) = y)
    (hq : ∀ y, HasDerivAt q (q' y) y)
    (hqp : ∀ y, HasDerivAt q' (q'' y) y)
    (hqpp : ∀ y, HasDerivAt q'' (q''' y) y)
    (hqne : ∀ y, q' y ≠ 0)
    (x : ℝ) :
    deriv (deriv (deriv X)) x =
      (3 * (q'' (X x)) ^ 2 - q' (X x) * q''' (X x)) /
        (q' (X x)) ^ 5 := by
  let w : ℝ → ℝ := fun z => (q' (X z))⁻¹
  have hXderiv (z : ℝ) :
      HasDerivAt X ((q' (X z))⁻¹) z := by
    exact HasDerivAt.of_local_left_inverse (hXcont.continuousAt)
      (hq (X z)) (hqne (X z)) (Filter.Eventually.of_forall hleft)
  have hwderiv (z : ℝ) :
      HasDerivAt w (-q'' (X z) / (q' (X z)) ^ 3) z := by
    have hcomp : HasDerivAt (fun t => q' (X t))
        (q'' (X z) * (q' (X z))⁻¹) z := by
      simpa [Function.comp_def] using (hqp (X z)).comp z (hXderiv z)
    have hinv := hcomp.inv (hqne (X z))
    change HasDerivAt ((fun t => q' (X t))⁻¹)
      (-q'' (X z) / (q' (X z)) ^ 3) z
    have hscalar :
        -q'' (X z) / (q' (X z)) ^ 3 =
          -(q'' (X z) * (q' (X z))⁻¹) / (q' (X z)) ^ 2 := by
      field_simp [hqne (X z)]
    simpa only [hscalar] using hinv
  have hderiv_eq : deriv w = (fun z => -q'' (X z) / (q' (X z)) ^ 3) := by
    funext z
    exact (hwderiv z).deriv
  have hcomp1 : HasDerivAt (fun t => q' (X t))
      (q'' (X x) * (q' (X x))⁻¹) x := by
    simpa [Function.comp_def] using (hqp (X x)).comp x (hXderiv x)
  have hcomp2 : HasDerivAt (fun t => q'' (X t))
      (q''' (X x) * (q' (X x))⁻¹) x := by
    simpa [Function.comp_def] using (hqpp (X x)).comp x (hXderiv x)
  have hpow : HasDerivAt (fun t => (q' (X t)) ^ 3)
      (3 * (q' (X x)) ^ (3 - 1) *
        (q'' (X x) * (q' (X x))⁻¹)) x := by
    simpa [Function.comp_def] using hcomp1.fun_pow 3
  have hquot := hcomp2.div hpow (by simp [hqne (X x)])
  have hv : HasDerivAt (fun t => -q'' (X t) / (q' (X t)) ^ 3)
      ((3 * (q'' (X x)) ^ 2 - q' (X x) * q''' (X x)) /
        (q' (X x)) ^ 5) x := by
    have hneg := hquot.neg
    have hneg' : HasDerivAt
        (fun t => -q'' (X t) / (q' (X t)) ^ 3)
        (-((q''' (X x) * (q' (X x))⁻¹ * (q' (X x)) ^ 3 -
          q'' (X x) * (3 * (q' (X x)) ^ (3 - 1) *
            (q'' (X x) * (q' (X x))⁻¹))) /
          ((q' (X x)) ^ 3) ^ 2)) x := by
      apply hneg.congr_of_eventuallyEq
      filter_upwards [] with t
      simp only [Pi.neg_apply, Pi.div_apply]
      ring
    have hscalar :
        (3 * (q'' (X x)) ^ 2 - q' (X x) * q''' (X x)) /
            (q' (X x)) ^ 5 =
          -((q''' (X x) * (q' (X x))⁻¹ * (q' (X x)) ^ 3 -
            q'' (X x) * (3 * (q' (X x)) ^ (3 - 1) *
              (q'' (X x) * (q' (X x))⁻¹))) /
            ((q' (X x)) ^ 3) ^ 2) := by
      field_simp [hqne (X x)]
      ring
    simpa only [hscalar] using hneg'
  have hderivX_eq : deriv X = w := by
    funext z
    exact (hXderiv z).deriv
  rw [hderivX_eq, hderiv_eq]
  exact hv.deriv

end MathlibPlus.Analysis.Claim21423
