import Mathlib

/-!
# Verified-height Gaussian order width

Formalization of admitted claim 4181.  The displayed width is represented by
`orderWidth d x = √(d * x)`.  The source does not state positivity of `d`; the
strict upper bound below therefore keeps exactly the displayed hypothesis.  Its
last sentence is a divergence assertion, which is valid under the explicit
positive-scale condition in `orderWidth_tendsto_atTop`.
-/

namespace MathlibPlus.Analysis.VerifiedHeightGaussianWidth

open Filter Topology

/-- The numerical verified-height threshold `T₀ = 3000175332800`. -/
def verifiedHeightT0 : ℝ := 3000175332800

/-- The one-standard-deviation order width `√(d x)`. -/
noncomputable def orderWidth (d x : ℝ) : ℝ := Real.sqrt (d * x)

/-- If `d < T₀⁻²` and `x > 0`, the displayed width bound holds. -/
theorem orderWidth_lt_verifiedHeight_bound {d x : ℝ}
    (hd : d < verifiedHeightT0⁻¹ ^ 2) (hx : 0 < x) :
    orderWidth d x < verifiedHeightT0⁻¹ * Real.sqrt x := by
  have hT : 0 < verifiedHeightT0 := by
    norm_num [verifiedHeightT0]
  have hTi : 0 < verifiedHeightT0⁻¹ := inv_pos.mpr hT
  have hsq : d * x < (verifiedHeightT0⁻¹ * Real.sqrt x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hx.le]
    exact mul_lt_mul_of_pos_right hd hx
  have hright : 0 < verifiedHeightT0⁻¹ * Real.sqrt x :=
    mul_pos hTi (Real.sqrt_pos.2 hx)
  by_cases hdx : 0 ≤ d * x
  · have hleft : 0 ≤ Real.sqrt (d * x) := Real.sqrt_nonneg _
    have hleftsq : (Real.sqrt (d * x)) ^ 2 = d * x := Real.sq_sqrt hdx
    dsimp [orderWidth]
    nlinarith
  · change Real.sqrt (d * x) < verifiedHeightT0⁻¹ * Real.sqrt x
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hdx)]
    exact hright

/-- For a positive scale parameter, the absolute width diverges with `x`. -/
theorem orderWidth_tendsto_atTop {d : ℝ} (hd : 0 < d) :
    Filter.Tendsto (fun x : ℝ => orderWidth d x) Filter.atTop Filter.atTop := by
  have hconst : Filter.Tendsto (fun _ : ℝ => Real.sqrt d) Filter.atTop
      (𝓝 (Real.sqrt d)) := tendsto_const_nhds
  have h := hconst.pos_mul_atTop (Real.sqrt_pos.2 hd) Real.tendsto_sqrt_atTop
  simpa [orderWidth, Real.sqrt_mul (le_of_lt hd), mul_comm] using h

end MathlibPlus.Analysis.VerifiedHeightGaussianWidth
