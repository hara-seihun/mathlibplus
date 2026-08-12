import Mathlib

namespace MathlibPlus.Analysis

/-!
Formalization of admitted claim 1109.  The logarithmic implication retains
all of the source inequalities, the rational identity is stated on its
source domain `σ < 2`, and the final monotonicity is on `Set.Iio 2`.
-/

/-- The logarithmic corollary, rational identity, and decreasing envelope. -/
theorem logarithmicCorollary_claim1109 :
    (∀ h T : ℝ, 0 < h → h ≤ 1 → 1 < T → 1 < h * T →
        0 < Real.log (h * T) ∧ Real.log (h * T) ≤ Real.log T) ∧
      (∀ σ : ℝ, σ < 2 →
        (7 - 5 * σ) / (2 - σ) - 1 - (2 * σ - 1) / (2 - σ) =
          6 * (1 - σ) / (2 - σ)) ∧
      StrictAntiOn (fun σ : ℝ => 6 * (1 - σ) / (2 - σ)) (Set.Iio 2) := by
  constructor
  · intro h T hhpos hhupper hT hprod
    constructor
    · exact Real.log_pos hprod
    · have hTpos : 0 < T := by linarith
      by_cases hh : h < 1
      · have hlt : h * T < T := by
          nlinarith [mul_pos (sub_pos.mpr hh) hTpos]
        have hprodpos : 0 < h * T := by linarith
        exact (Real.strictMonoOn_log hprodpos hTpos hlt).le
      · have hh_eq : h = 1 := by linarith
        simpa [hh_eq]
  · constructor
    · intro σ hσ
      have hden : 2 - σ ≠ 0 := ne_of_gt (by linarith)
      field_simp [hden]
      ring
    · intro x hx y hy hxy
      have hxden : 0 < 2 - x := by exact sub_pos.mpr hx
      have hyden : 0 < 2 - y := by exact sub_pos.mpr hy
      apply (div_lt_div_iff₀ hyden hxden).2
      nlinarith [hxy]

end MathlibPlus.Analysis
