import Mathlib

namespace MathlibPlus.Analysis.A4Kernel

private lemma cubicTaylor_le_exp {u : ℝ} (hu : 0 ≤ u) :
    1 + 2 * u + 2 * u ^ 2 + (4 / 3 : ℝ) * u ^ 3 ≤ Real.exp (2 * u) := by
  have h := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * u by positivity) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  convert h using 1 <;> ring

/-- The derivative of the two-correction Binet continuum datum is strictly
positive on the nonnegative ray. -/
theorem continuumDerivative_pos {u : ℝ} (hu : 0 ≤ u) :
    0 <
      (u + 1) * Real.exp u + Real.exp (-u) *
        (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
          (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4) := by
  have hTaylor := cubicTaylor_le_exp hu
  have hu1 : 0 < u + 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hTaylor hu1.le
  have hcert :
      0 < (224 * u ^ 4 + 664 * u ^ 3 + 780 * u ^ 2 + 330 * u + 315) / 180 := by
    positivity
  let c :=
    (u + 1) * Real.exp u + Real.exp (-u) *
      (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
        (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4)
  have hc_mul : 0 < c * Real.exp u := by
    rw [show c * Real.exp u =
      (u + 1) * Real.exp (2 * u) +
        (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
          (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4) by
      dsimp [c]
      rw [add_mul]
      calc
        (u + 1) * Real.exp u * Real.exp u +
            Real.exp (-u) *
              (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
                (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4) * Real.exp u =
          (u + 1) * (Real.exp u * Real.exp u) +
            (Real.exp (-u) * Real.exp u) *
              (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
                (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4) := by ring_nf
        _ = (u + 1) * Real.exp (2 * u) +
            (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
              (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4) := by
          rw [show Real.exp u * Real.exp u = Real.exp (2 * u) by
                rw [← Real.exp_add]
                congr 1 <;> ring,
              show Real.exp (-u) * Real.exp u = 1 by
                rw [← Real.exp_add]
                simp]
          simp]
    nlinarith
  exact pos_of_mul_pos_left hc_mul (Real.exp_pos u).le

/-- The A4 continuum kernel `c(x + y) + c(|x - y|)` is strictly positive on
`[0, α]²` for every positive `α`. -/
theorem continuumKernel_pos {α x y : ℝ} (_hα : 0 < α)
    (hx : x ∈ Set.Icc 0 α) (hy : y ∈ Set.Icc 0 α) :
    let c : ℝ → ℝ := fun u =>
      (u + 1) * Real.exp u + Real.exp (-u) *
        (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
          (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4)
    0 < c (x + y) + c |x - y| := by
  dsimp only
  exact add_pos (continuumDerivative_pos (by linarith [hx.1, hy.1]))
    (continuumDerivative_pos (abs_nonneg _))

end MathlibPlus.Analysis.A4Kernel
