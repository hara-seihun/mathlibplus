import Mathlib.MeasureTheory.Integral.Gamma

namespace MathlibPlus.Probability.Claim10504

open _root_.Set

/-- The normalized moments of the unit-scale Gamma density are its rising
factorials.  This is the integral form of the admitted claim 10504. -/
theorem gammaMomentFormula_claim10504 {α : ℝ} (hα : 0 < α) (n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (x ^ n) * (x ^ (α - 1) * Real.exp (-x) / Real.Gamma α)) =
      ∏ u ∈ Finset.range n, (α + (u : ℝ)) := by
  have hΓ : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα).ne'
  have hgamma : ∀ m : ℕ,
      Real.Gamma (α + (m : ℝ)) =
        Real.Gamma α * (∏ u ∈ Finset.range m, (α + (u : ℝ))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hmpos : 0 < α + (m : ℝ) := by positivity
        have hrec := Real.Gamma_add_one hmpos.ne'
        rw [Finset.prod_range_succ]
        rw [show α + (↑(Nat.succ m) : ℝ) = (α + (m : ℝ)) + 1 by push_cast; ring]
        rw [hrec, ih]
        ring
  have hmain :
      (∫ x : ℝ in Ioi 0,
        (x ^ n) * (x ^ (α - 1) * Real.exp (-x))) =
        Real.Gamma (α + (n : ℝ)) := by
    convert Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := α + (n : ℝ)) (r := 1) (by positivity) one_pos using 1
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp
      have hx' : 0 < x := hx
      rw [← Real.rpow_natCast]
      rw [show α + (n : ℝ) - 1 = (n : ℝ) + (α - 1) by ring]
      rw [Real.rpow_add hx']
      simp only [one_mul]
      ring
    · norm_num
  calc
    (∫ x : ℝ in Ioi 0,
        (x ^ n) * (x ^ (α - 1) * Real.exp (-x) / Real.Gamma α)) =
        (1 / Real.Gamma α) *
          (∫ x : ℝ in Ioi 0,
            (x ^ n) * (x ^ (α - 1) * Real.exp (-x))) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      field_simp
    _ = (1 / Real.Gamma α) * Real.Gamma (α + (n : ℝ)) := by rw [hmain]
    _ = ∏ u ∈ Finset.range n, (α + (u : ℝ)) := by
      rw [hgamma]
      field_simp

end MathlibPlus.Probability.Claim10504
