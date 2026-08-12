import Mathlib

namespace MathlibPlus.Analysis.Claim47648

/-!
Formalization of admitted claim 47648.  The source's bounded maps are represented
by continuous linear maps, and its left-inverse identity is stated pointwise.
The source's `x_U = exp (δ U) x₀` is real scalar multiplication.
-/

/-- A left inverse forces the forward image of an exponentially scaled nonzero
vector to have the reciprocal left-inverse norm lower bound. -/
theorem leftInverseGrowth_lowerBound_claim47648
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (E : X →L[ℂ] Y) (D : Y →L[ℂ] X)
    (hDE : ∀ x : X, D (E x) = x)
    (δ U : ℝ) (_hδ : 0 < δ) (x₀ : X) (hx₀ : x₀ ≠ 0) :
    ‖E (Real.exp (δ * U) • x₀)‖ ≥
      Real.exp (δ * U) * ‖x₀‖ / ‖D‖ := by
  have hD_ne : D ≠ 0 := by
    intro hD
    apply hx₀
    simpa [hD] using (hDE x₀).symm
  have hD_pos : 0 < ‖D‖ := norm_pos_iff.mpr hD_ne
  have hbound : ‖Real.exp (δ * U) • x₀‖ ≤
      ‖D‖ * ‖E (Real.exp (δ * U) • x₀)‖ := by
    calc
      ‖Real.exp (δ * U) • x₀‖ =
          ‖D (E (Real.exp (δ * U) • x₀))‖ := by
            rw [hDE]
      _ ≤ ‖D‖ * ‖E (Real.exp (δ * U) • x₀)‖ := D.le_opNorm _
  have hscale : ‖Real.exp (δ * U) • x₀‖ =
      Real.exp (δ * U) * ‖x₀‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [ge_iff_le]
  apply (div_le_iff₀ hD_pos).2
  calc
    Real.exp (δ * U) * ‖x₀‖ = ‖Real.exp (δ * U) • x₀‖ := hscale.symm
    _ ≤ ‖D‖ * ‖E (Real.exp (δ * U) • x₀)‖ := hbound
    _ = ‖E (Real.exp (δ * U) • x₀)‖ * ‖D‖ := by ring

end MathlibPlus.Analysis.Claim47648
