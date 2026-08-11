import Mathlib

/-!
# Final Hankel defect

The symmetrized integral identity extracted from legacy packet `C-0010`.
-/

open MeasureTheory

namespace MathlibPlus.MomentGeometry

noncomputable section

/-- The final `2 × 2` Hankel defect is half the double integral of
`x³ y³ (x-y)²`. -/
theorem finalHankelDefectIdentity (μ : Measure ℝ)
    (hint : ∀ j ≤ 5, Integrable (fun x : ℝ => x ^ j) μ) :
    (∫ x : ℝ, x ^ 3 ∂μ) * (∫ x : ℝ, x ^ 5 ∂μ) -
        (∫ x : ℝ, x ^ 4 ∂μ) ^ 2 =
      (1 / 2 : ℝ) * ∫ x : ℝ, ∫ y : ℝ,
        x ^ 3 * y ^ 3 * (x - y) ^ 2 ∂μ ∂μ := by
  have h3 : Integrable (fun x : ℝ => x ^ 3) μ := hint 3 (by norm_num)
  have h4 : Integrable (fun x : ℝ => x ^ 4) μ := hint 4 (by norm_num)
  have h5 : Integrable (fun x : ℝ => x ^ 5) μ := hint 5 (by norm_num)
  let m3 : ℝ := ∫ x : ℝ, x ^ 3 ∂μ
  let m4 : ℝ := ∫ x : ℝ, x ^ 4 ∂μ
  let m5 : ℝ := ∫ x : ℝ, x ^ 5 ∂μ
  have hinner (x : ℝ) :
      (∫ y : ℝ, x ^ 3 * y ^ 3 * (x - y) ^ 2 ∂μ) =
        x ^ 5 * m3 - (2 * x ^ 4) * m4 + x ^ 3 * m5 := by
    have hA : Integrable (fun y : ℝ => x ^ 5 * y ^ 3) μ := h3.const_mul _
    have hB : Integrable (fun y : ℝ => (2 * x ^ 4) * y ^ 4) μ := h4.const_mul _
    have hC : Integrable (fun y : ℝ => x ^ 3 * y ^ 5) μ := h5.const_mul _
    calc
      (∫ y : ℝ, x ^ 3 * y ^ 3 * (x - y) ^ 2 ∂μ) =
          ∫ y : ℝ, (x ^ 5 * y ^ 3 - (2 * x ^ 4) * y ^ 4) +
            x ^ 3 * y ^ 5 ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              ring
      _ = (∫ y : ℝ, x ^ 5 * y ^ 3 - (2 * x ^ 4) * y ^ 4 ∂μ) +
          ∫ y : ℝ, x ^ 3 * y ^ 5 ∂μ := integral_add (hA.sub hB) hC
      _ = ((∫ y : ℝ, x ^ 5 * y ^ 3 ∂μ) -
          ∫ y : ℝ, (2 * x ^ 4) * y ^ 4 ∂μ) +
          ∫ y : ℝ, x ^ 3 * y ^ 5 ∂μ := by rw [integral_sub hA hB]
      _ = x ^ 5 * m3 - (2 * x ^ 4) * m4 + x ^ 3 * m5 := by
          simp only [integral_const_mul]
          rfl
  rw [show (∫ x : ℝ, ∫ y : ℝ, x ^ 3 * y ^ 3 * (x - y) ^ 2 ∂μ ∂μ) =
      ∫ x : ℝ, (x ^ 5 * m3 - (2 * x ^ 4) * m4) + x ^ 3 * m5 ∂μ by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hinner x]
  have hA : Integrable (fun x : ℝ => x ^ 5 * m3) μ := h5.mul_const _
  have hB : Integrable (fun x : ℝ => (2 * x ^ 4) * m4) μ :=
    (h4.const_mul 2).mul_const _
  have hC : Integrable (fun x : ℝ => x ^ 3 * m5) μ := h3.mul_const _
  have houter :
      (∫ x : ℝ, (x ^ 5 * m3 - (2 * x ^ 4) * m4) + x ^ 3 * m5 ∂μ) =
        m5 * m3 - (2 * m4) * m4 + m3 * m5 := by
    calc
      _ = (∫ x : ℝ, x ^ 5 * m3 - (2 * x ^ 4) * m4 ∂μ) +
          ∫ x : ℝ, x ^ 3 * m5 ∂μ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using integral_add (hA.sub hB) hC
      _ = ((∫ x : ℝ, x ^ 5 * m3 ∂μ) -
          ∫ x : ℝ, (2 * x ^ 4) * m4 ∂μ) +
          ∫ x : ℝ, x ^ 3 * m5 ∂μ := by rw [integral_sub hA hB]
      _ = m5 * m3 - (2 * m4) * m4 + m3 * m5 := by
          simp only [integral_mul_const, integral_const_mul]
          dsimp [m3, m4, m5]
  rw [houter]
  dsimp [m3, m4, m5]
  ring

end

end MathlibPlus.MomentGeometry
