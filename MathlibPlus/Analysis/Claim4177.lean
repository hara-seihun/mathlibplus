import Mathlib

namespace MathlibPlus.Analysis.Claim4177

/-- The canonical real function with derivative `log (d / q)` and value `κ` at `d`. -/
theorem peak_eq_kappa_iff {d κ q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    (κ + q * Real.log (d / q) + q - d) = κ ↔ q = d := by
  constructor
  · intro h
    by_contra hqd
    have hdq : d / q ≠ 1 := by
      intro h
      apply hqd
      have hdq' : d = q := (div_eq_one_iff_eq (ne_of_gt hq)).mp h
      exact hdq'.symm
    have hlog : Real.log (d / q) < d / q - 1 :=
      Real.log_lt_sub_one_of_pos (div_pos hd hq) hdq
    have hmul : q * Real.log (d / q) < d - q := by
      calc
        q * Real.log (d / q) < q * (d / q - 1) := (mul_lt_mul_of_pos_left hlog hq)
        _ = d - q := by field_simp
    linarith
  · intro h
    subst q
    simp

theorem peak_le_kappa {d κ q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    κ + q * Real.log (d / q) + q - d ≤ κ := by
  have hlog : Real.log (d / q) ≤ d / q - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hd hq)
  have hmul : q * Real.log (d / q) ≤ d - q := by
    calc
      q * Real.log (d / q) ≤ q * (d / q - 1) := (mul_le_mul_of_nonneg_left hlog (le_of_lt hq))
      _ = d - q := by field_simp
  linarith

theorem deriv_peak {d κ q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    deriv (fun x : ℝ => κ + x * Real.log (d / x) + x - d) q = Real.log (d / q) := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hdq : d / q ≠ 0 := ne_of_gt (div_pos hd hq)
  have hdiv := (hasDerivAt_const q d).div (hasDerivAt_id q) hq0
  have hlog := (Real.hasDerivAt_log hdq).comp q hdiv
  have h : HasDerivAt
      (((fun x : ℝ => κ) + id * (Real.log ∘ HDiv.hDiv d)) + id - (fun _ => d))
      (0 + (1 * (Real.log ∘ HDiv.hDiv d) q +
        id q * ((d / q)⁻¹ * ((0 * id q - d * 1) / id q ^ 2))) + 1 - 0) q := by
    exact (((hasDerivAt_const q κ).add ((hasDerivAt_id q).mul hlog)).add
      (hasDerivAt_id q)).sub (hasDerivAt_const q d)
  have hfun : (fun x : ℝ => κ + x * Real.log (d / x) + x - d) =
      ((fun x : ℝ => κ) + id * (Real.log ∘ HDiv.hDiv d)) + id - (fun _ => d) := by
    funext x
    simp [Function.comp_def, id]
  rw [hfun, h.deriv]
  simp [id]
  field_simp [hq0, ne_of_gt hd]
  ring

theorem deriv_deriv_peak {d κ q : ℝ} (hd : 0 < d) (hq : 0 < q) :
    deriv (fun x : ℝ => deriv (fun y : ℝ => κ + y * Real.log (d / y) + y - d) x) q = -1 / q := by
  have hEq : (fun x : ℝ => deriv (fun y : ℝ => κ + y * Real.log (d / y) + y - d) x) =ᶠ[nhds q]
      (Real.log ∘ HDiv.hDiv d) := by
    filter_upwards [eventually_gt_nhds hq] with x hx
    rw [deriv_peak hd hx]
    rfl
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hdq : d / q ≠ 0 := ne_of_gt (div_pos hd hq)
  have hdiv := (hasDerivAt_const q d).div (hasDerivAt_id q) hq0
  have hlog := (Real.hasDerivAt_log hdq).comp q hdiv
  rw [hEq.deriv_eq, hlog.deriv]
  field_simp [hq0, ne_of_gt hd]
  simp [id]
  ring

theorem second_deriv_peak_at_d {d κ : ℝ} (hd : 0 < d) :
    deriv (fun x : ℝ => deriv (fun y : ℝ => κ + y * Real.log (d / y) + y - d) x) d = -1 / d :=
  deriv_deriv_peak hd hd

end MathlibPlus.Analysis.Claim4177
