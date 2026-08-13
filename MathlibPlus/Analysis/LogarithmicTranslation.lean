import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

open MeasureTheory
open scoped ENNReal

namespace MathlibPlus.Analysis.LogarithmicTranslation

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-!
The logarithmic translation on `L²(ℝ, dx)` is represented on the quotient of
almost-everywhere equal functions by `Lp.compMeasurePreserving`.  The explicit
linear-isometry equivalence records the word “unitary” in the source claim.
-/

/-- Composition with a real translation on `L²(ℝ, dx)`. -/
noncomputable def logarithmicTranslationLinear (a : ℝ) : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + a)
    (measurePreserving_add_right (volume : Measure ℝ) a)

theorem logarithmicTranslationLinear_comp (a b : ℝ) (f : H) :
    logarithmicTranslationLinear a (logarithmicTranslationLinear b f) =
      logarithmicTranslationLinear (b + a) f := by
  change Lp.compMeasurePreserving (fun x : ℝ => x + a)
      (measurePreserving_add_right (volume : Measure ℝ) a)
      (Lp.compMeasurePreserving (fun x : ℝ => x + b)
        (measurePreserving_add_right (volume : Measure ℝ) b) f) =
    Lp.compMeasurePreserving (fun x : ℝ => x + (b + a))
      (measurePreserving_add_right (volume : Measure ℝ) (b + a)) f
  simpa [Function.comp_def, add_assoc, add_comm, add_left_comm] using
    (Lp.compMeasurePreserving_comp_apply f
      (measurePreserving_add_right (volume : Measure ℝ) b)
      (measurePreserving_add_right (volume : Measure ℝ) a)).symm

theorem logarithmicTranslationLinear_zero (f : H) :
    logarithmicTranslationLinear 0 f = f := by
  change Lp.compMeasurePreserving (fun x : ℝ => x + 0)
      (measurePreserving_add_right (volume : Measure ℝ) 0) f = f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      (measurePreserving_add_right (volume : Measure ℝ) 0)] with x hx
  simpa [Function.comp_def] using hx

/-- The unitary logarithmic translation `f(x) ↦ f(x+a)`. -/
noncomputable def logarithmicTranslation (a : ℝ) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (logarithmicTranslationLinear a) (by
    intro f
    refine ⟨logarithmicTranslationLinear (-a) f, ?_⟩
    rw [logarithmicTranslationLinear_comp, neg_add_cancel]
    exact logarithmicTranslationLinear_zero f)

theorem logarithmicTranslation_coeFn (a : ℝ) (f : H) :
    logarithmicTranslation a f =ᵐ[(volume : Measure ℝ)] fun x : ℝ => f (x + a) := by
  change Lp.compMeasurePreserving (fun x : ℝ => x + a)
      (measurePreserving_add_right (volume : Measure ℝ) a) f =ᵐ[_] _
  exact Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_right (volume : Measure ℝ) a)

theorem logarithmicTranslation_norm (a : ℝ) (f : H) :
    ‖logarithmicTranslation a f‖ = ‖f‖ := by
  exact LinearIsometryEquiv.norm_map _ _

/-- Claim 9811: the logarithmic translation is unitary and preserves the `L²` norm. -/
theorem logarithmicTranslation_claim9811 (a : ℝ) (f : H) :
    (logarithmicTranslation a f =ᵐ[(volume : Measure ℝ)] fun x : ℝ => f (x + a)) ∧
      ‖logarithmicTranslation a f‖ = ‖f‖ := by
  exact ⟨logarithmicTranslation_coeFn a f, logarithmicTranslation_norm a f⟩

/-- Claim 9812: a unitary translation has the universal scalar defect floor. -/
theorem logarithmicTranslation_scalar_defect_claim9812 (a : ℝ) (_ha : a ≠ 0) (z : ℂ)
    (f : H) :
    |‖z‖ - 1| * ‖f‖ ≤ ‖logarithmicTranslation a f - z • f‖ := by
  have h := abs_norm_sub_norm_le (logarithmicTranslation a f) (z • f)
  rw [logarithmicTranslation_norm, norm_smul] at h
  have hfactor : |‖f‖ - ‖z‖ * ‖f‖| = |‖z‖ - 1| * ‖f‖ := by
    rw [show ‖f‖ - ‖z‖ * ‖f‖ = (1 - ‖z‖) * ‖f‖ by ring]
    rw [abs_mul, abs_of_nonneg (norm_nonneg f)]
    rw [abs_sub_comm]
  simpa [hfactor] using h

/-- The positive-rational logarithmic translation representation from claim
48147. The existing `logarithmicTranslation` is the unitary representative
on the complex `L²` quotient; this theorem restricts its parameter group to
positive rationals and records its pointwise representative almost everywhere.
-/
theorem rationalLogarithmicTranslation_claim48147
    (r s : ℚ) (hr : 0 < r) (hs : 0 < s) (f : H) :
    (logarithmicTranslation (Real.log (r : ℝ)) f =ᵐ[(volume : Measure ℝ)]
        fun u : ℝ => f (u + Real.log (r : ℝ))) ∧
      (‖logarithmicTranslation (Real.log (r : ℝ)) f‖ = ‖f‖) ∧
      logarithmicTranslation (Real.log (r : ℝ))
          (logarithmicTranslation (Real.log (s : ℝ)) f) =
        logarithmicTranslation (Real.log ((r * s : ℚ) : ℝ)) f := by
  refine ⟨logarithmicTranslation_coeFn _ _, ?_⟩
  constructor
  · exact logarithmicTranslation_norm _ _
  · change logarithmicTranslationLinear (Real.log (r : ℝ))
        (logarithmicTranslationLinear (Real.log (s : ℝ)) f) =
      logarithmicTranslationLinear (Real.log ((r * s : ℚ) : ℝ)) f
    rw [logarithmicTranslationLinear_comp]
    have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hrne : (r : ℝ) ≠ 0 := ne_of_gt hr'
    have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs'
    have hlog : Real.log ((r * s : ℚ) : ℝ) =
        Real.log (s : ℝ) + Real.log (r : ℝ) := by
      rw [Rat.cast_mul, Real.log_mul hrne hsne]
      exact add_comm _ _
    rw [hlog]

end MathlibPlus.Analysis.LogarithmicTranslation
