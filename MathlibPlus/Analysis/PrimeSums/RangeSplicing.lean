import Mathlib

/-!
# Splicing a finite positive range to an analytic prime-sum tail

The theorem below isolates the exact range-splicing step at `10^8`.  The function
argument is the normalized reciprocal-prime error in the intended application.
-/

namespace MathlibPlus.Analysis.PrimeSums

/-- Finite positivity through `10^8` and the global Axler-shaped lower estimate splice
to the strict same-shape bound with coefficient obtained at the cutoff. -/
theorem rangeSplicing
    (A₁ : ℝ → ℝ)
    (hfinite : ∀ x : ℝ, 1 < x → x ≤ (10 : ℝ) ^ 8 → 0 < A₁ x)
    (hglobal : ∀ x : ℝ, 1 < x →
      -1 / (20 * Real.log x ^ 3) - 3 / (16 * Real.log x ^ 4) ≤ A₁ x) :
    ∀ x : ℝ, 1 < x →
      -(1 / (20 * Real.log ((10 : ℝ) ^ 8)) +
          3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2)) / Real.log x ^ 2 < A₁ x := by
  intro x hx
  have hlogX : 0 < Real.log x := Real.log_pos hx
  rcases le_or_gt x ((10 : ℝ) ^ 8) with hxcut | hcutx
  · have hCpos :
        0 < 1 / (20 * Real.log ((10 : ℝ) ^ 8)) +
          3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2) := by
      positivity
    have hLsq : 0 < Real.log x ^ 2 := by
      positivity
    have hneg :
        -(1 / (20 * Real.log ((10 : ℝ) ^ 8)) +
            3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2)) / Real.log x ^ 2 < 0 := by
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hCpos) hLsq
    exact hneg.trans (hfinite x hx hxcut)
  · have hlogCut : 0 < Real.log ((10 : ℝ) ^ 8) := by
      positivity
    have hloglt : Real.log ((10 : ℝ) ^ 8) < Real.log x :=
      Real.strictMonoOn_log
        (show 0 < (10 : ℝ) ^ 8 by positivity)
        (show 0 < x by linarith)
        hcutx
    have hden₁ :
        20 * Real.log ((10 : ℝ) ^ 8) < 20 * Real.log x :=
      mul_lt_mul_of_pos_left hloglt (by norm_num)
    have hterm₁ :
        1 / (20 * Real.log x) < 1 / (20 * Real.log ((10 : ℝ) ^ 8)) :=
      one_div_lt_one_div_of_lt (by positivity) hden₁
    have hsq : Real.log ((10 : ℝ) ^ 8) ^ 2 < Real.log x ^ 2 := by
      nlinarith
    have hden₂ :
        16 * Real.log ((10 : ℝ) ^ 8) ^ 2 < 16 * Real.log x ^ 2 :=
      mul_lt_mul_of_pos_left hsq (by norm_num)
    have hterm₂ :
        3 / (16 * Real.log x ^ 2) <
          3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2) :=
      div_lt_div_of_pos_left (by norm_num) (by positivity) hden₂
    have hg :
        1 / (20 * Real.log x) + 3 / (16 * Real.log x ^ 2) <
          1 / (20 * Real.log ((10 : ℝ) ^ 8)) +
            3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2) :=
      add_lt_add hterm₁ hterm₂
    have hdiv :
        -(1 / (20 * Real.log ((10 : ℝ) ^ 8)) +
            3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2)) / Real.log x ^ 2 <
          -(1 / (20 * Real.log x) + 3 / (16 * Real.log x ^ 2)) /
            Real.log x ^ 2 :=
      (div_lt_div_iff_of_pos_right (by positivity)).2 (neg_lt_neg hg)
    have hrearrange :
        -(1 / (20 * Real.log x) + 3 / (16 * Real.log x ^ 2)) /
            Real.log x ^ 2 =
          -1 / (20 * Real.log x ^ 3) - 3 / (16 * Real.log x ^ 4) := by
      field_simp
      <;> ring
    calc
      -(1 / (20 * Real.log ((10 : ℝ) ^ 8)) +
          3 / (16 * Real.log ((10 : ℝ) ^ 8) ^ 2)) / Real.log x ^ 2 <
          -(1 / (20 * Real.log x) + 3 / (16 * Real.log x ^ 2)) /
            Real.log x ^ 2 := hdiv
      _ = -1 / (20 * Real.log x ^ 3) - 3 / (16 * Real.log x ^ 4) := hrearrange
      _ ≤ A₁ x := hglobal x hx

end MathlibPlus.Analysis.PrimeSums
