import Mathlib

/-!
# Normalized moments

Scale-free moment coordinates extracted from legacy packet `C-0010`.
-/

open MeasureTheory

namespace MathlibPlus.MomentGeometry

noncomputable section

/-- The `j`th real moment of a measure, using mathlib's Bochner integral convention. -/
def moment (μ : Measure ℝ) (j : ℕ) : ℝ :=
  ∫ x, x ^ j ∂μ

/-- The scale-free ratio `m₀ m₂ / m₁²`. Its intended use assumes a nonzero first
moment and a finite second moment; the total definition is convenient for algebra. -/
def normalizedVariance (μ : Measure ℝ) : ℝ :=
  moment μ 0 * moment μ 2 / moment μ 1 ^ 2

/-- After normalizing the measure to total mass one, the normalized moment ratio
is one plus variance divided by the square of the mean. -/
theorem normalizedVariance_eq_one_add_variance
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hfirst : moment μ 1 ≠ 0) :
    normalizedVariance μ =
      1 + ProbabilityTheory.variance (fun x : ℝ => x) μ / moment μ 1 ^ 2 := by
  have hid : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hsecond
  have hfirst' : (∫ x : ℝ, x ∂μ) ≠ 0 := by
    simpa [moment] using hfirst
  rw [normalizedVariance, ProbabilityTheory.variance_eq_sub hid]
  simp only [moment, pow_zero, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, pow_one, Pi.pow_apply]
  field_simp [hfirst']
  ring

/-- For a finite positive measure supported on the nonnegative reals, with finite
second moment and nonzero first moment, the normalized variance is at least one. -/
theorem normalizedVariance_bound
    (μ : Measure ℝ) (hsupport : μ (Set.Iio 0) = 0)
    (hfinite : μ Set.univ ≠ ⊤)
    (hsecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hfirst : moment μ 1 ≠ 0) :
    1 ≤ normalizedVariance μ := by
  let _ : IsFiniteMeasure μ := IsFiniteMeasure.mk (lt_top_iff_ne_top.mpr hfinite)
  have hnonneg : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    simpa [Set.Iio, not_le] using hsupport
  have hid : MemLp (fun x : ℝ => x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hsecond
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hnonneg
    (by simpa using (memLp_const (μ := μ) (1 : ℝ))) (by simpa using hid)
  have hm0_nonneg : 0 ≤ moment μ 0 := by
    simp [moment]
  have hm2_nonneg : 0 ≤ moment μ 2 := by
    exact integral_nonneg (fun x => sq_nonneg x)
  have hm1_nonneg : 0 ≤ moment μ 1 := by
    rw [moment]
    apply integral_nonneg_of_ae
    filter_upwards [hnonneg] with x hx
    simpa using hx
  have hm1_le : moment μ 1 ≤ √(moment μ 0) * √(moment μ 2) := by
    simpa [moment, Real.sqrt_eq_rpow, Real.rpow_two] using hholder
  have hsquare : moment μ 1 ^ 2 ≤ moment μ 0 * moment μ 2 := by
    nlinarith [Real.sq_sqrt hm0_nonneg, Real.sq_sqrt hm2_nonneg,
      Real.sqrt_nonneg (moment μ 0), Real.sqrt_nonneg (moment μ 2)]
  rw [normalizedVariance]
  exact (le_div_iff₀ (sq_pos_of_ne_zero hfirst)).2 (by simpa using hsquare)

end

end MathlibPlus.MomentGeometry
