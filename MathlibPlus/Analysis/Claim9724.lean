import Mathlib

open Set MeasureTheory
open scoped Interval

namespace MathlibPlus.Analysis.Claim9724

private lemma reciprocalLog_strict (a x : ℝ) (ha : 1 < a) (hax : a < x) :
    1 / (x * Real.log x) < 1 / (a * Real.log a) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hx0 : 0 < x := lt_trans ha0 hax
  have hlog : Real.log a < Real.log x :=
    Real.strictMonoOn_log (by exact ha0) (by exact hx0) hax
  have hprod₁ : a * Real.log a < a * Real.log x :=
    mul_lt_mul_of_pos_left hlog ha0
  have hprod₂ : a * Real.log x < x * Real.log x :=
    mul_lt_mul_of_pos_right hax (Real.log_pos (lt_trans ha hax))
  exact one_div_lt_one_div_of_lt (mul_pos ha0 (Real.log_pos ha))
    (lt_trans hprod₁ hprod₂)

private lemma reciprocalLog_continuousOn (a b : ℝ) (ha : 1 < a) (_hab : a ≤ b) :
    ContinuousOn (fun x : ℝ => 1 / (x * Real.log x)) (Icc a b) := by
  have hsubset : Icc a b ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx
    exact ne_of_gt (lt_of_lt_of_le (lt_trans zero_lt_one ha) hx.1)
  have hlog : ContinuousOn Real.log (Icc a b) :=
    Real.continuousOn_log.mono hsubset
  have hden : ∀ x ∈ Icc a b, x * Real.log x ≠ 0 := by
    intro x hx
    exact mul_ne_zero (ne_of_gt (lt_of_lt_of_le (lt_trans zero_lt_one ha) hx.1))
      (ne_of_gt (Real.log_pos (lt_of_lt_of_le ha hx.1)))
  exact continuousOn_const.div₀ (continuousOn_id.mul hlog) hden

private lemma intervalAverage_lt_left (a L : ℝ) (ha : 1 < a) (hL : 0 < L) :
    (1 / L) * ∫ v in a..a + L, (1 / (v * Real.log v)) <
      1 / (a * Real.log a) := by
  have hab : a < a + L := by linarith
  have hfc := reciprocalLog_continuousOn a (a + L) ha hab.le
  have hgc : ContinuousOn (fun _ : ℝ => 1 / (a * Real.log a))
      (Icc a (a + L)) := continuousOn_const
  have hle : ∀ x ∈ Ioc a (a + L),
      1 / (x * Real.log x) ≤ 1 / (a * Real.log a) := by
    intro x hx
    exact (reciprocalLog_strict a x ha hx.1).le
  have hlt : ∃ x ∈ Icc a (a + L),
      1 / (x * Real.log x) < 1 / (a * Real.log a) := by
    refine ⟨(a + (a + L)) / 2, ?_, ?_⟩
    · constructor <;> linarith
    · apply reciprocalLog_strict a ((a + (a + L)) / 2) ha
      linarith
  have hInt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hfc hgc hle hlt
  have hscaled := mul_lt_mul_of_pos_left hInt (one_div_pos.mpr hL)
  calc
    (1 / L) * ∫ v in a..a + L, (1 / (v * Real.log v)) <
        (1 / L) * ∫ _v in a..a + L, (1 / (a * Real.log a)) := hscaled
    _ = 1 / (a * Real.log a) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp
      ring

private lemma intervalAverage_gt_right (a L : ℝ) (ha : 1 < a) (hL : 0 < L) :
    1 / ((a + L) * Real.log (a + L)) <
      (1 / L) * ∫ v in a..a + L, (1 / (v * Real.log v)) := by
  have hab : a < a + L := by linarith
  have hfc : ContinuousOn (fun _ : ℝ => 1 / ((a + L) * Real.log (a + L)))
      (Icc a (a + L)) := continuousOn_const
  have hgc := reciprocalLog_continuousOn a (a + L) ha hab.le
  have hle : ∀ x ∈ Ioc a (a + L),
      1 / ((a + L) * Real.log (a + L)) ≤ 1 / (x * Real.log x) := by
    intro x hx
    by_cases hxeq : x = a + L
    · simpa [hxeq]
    · have hxl : x < a + L := lt_of_le_of_ne hx.2 hxeq
      exact (reciprocalLog_strict x (a + L)
        (lt_of_lt_of_le ha (le_of_lt hx.1)) hxl).le
  have hlt : ∃ x ∈ Icc a (a + L),
      1 / ((a + L) * Real.log (a + L)) < 1 / (x * Real.log x) := by
    refine ⟨(a + (a + L)) / 2, ?_, ?_⟩
    · constructor <;> linarith
    · apply reciprocalLog_strict ((a + (a + L)) / 2) (a + L)
        (by linarith [ha])
      linarith
  have hInt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hfc hgc hle hlt
  have hscaled := mul_lt_mul_of_pos_left hInt (one_div_pos.mpr hL)
  calc
    1 / ((a + L) * Real.log (a + L)) = (1 / L) *
        ∫ _v in a..a + L, (1 / ((a + L) * Real.log (a + L))) := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          field_simp
          ring
    _ < (1 / L) * ∫ v in a..a + L, (1 / (v * Real.log v)) := hscaled

/-- Claim 9724, with the interval average written inline so no auxiliary
private definition leaks into the public theorem type. -/
theorem strictIntervalAverageSandwich :
  ∀ (p : ℕ), Nat.Prime p → ∀ y : ℝ, y - Real.log (p : ℝ) > 1 →
    let L : ℝ := Real.log (p : ℝ)
    let η : ℝ → ℝ := fun x ↦
      (1 / L) * ∫ v in x..x + L, (1 / (v * Real.log v))
    η y < 1 / (y * Real.log y) ∧
      1 / (y * Real.log y) < η (y - L) := by
  intro p hp y hy
  dsimp
  have hL : 0 < Real.log (p : ℝ) := hp.log_pos
  have hleft : 1 < y := by
    have : 1 < y - Real.log (p : ℝ) := hy
    linarith [hL]
  have hbase : 1 < y - Real.log (p : ℝ) := hy
  constructor
  · exact intervalAverage_lt_left y (Real.log (p : ℝ)) hleft hL
  · have hright := intervalAverage_gt_right (y - Real.log (p : ℝ))
      (Real.log (p : ℝ)) hbase hL
    simpa [sub_add_cancel] using hright

end MathlibPlus.Analysis.Claim9724
