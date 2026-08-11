import MathlibPlus.Basic

open MeasureTheory

namespace MathlibPlus.Analysis.Claim2312

 theorem zero_integral_two_mode
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (h₀ h₄ : α → ℝ)
    (h₀_int : Integrable h₀ μ) (h₄_int : Integrable h₄ μ)
    (hden : (∫ x, h₀ x ∂μ) ≠ 0) :
    let a : ℝ := (∫ x, h₄ x ∂μ) / (∫ x, h₀ x ∂μ)
    let h : α → ℝ := fun x => h₄ x - a * h₀ x
    (∫ x, h x ∂μ) = 0 := by
  dsimp
  have hscale : Integrable (fun x =>
      ((∫ y, h₄ y ∂μ) / (∫ y, h₀ y ∂μ)) * h₀ x) μ :=
    h₀_int.const_mul _
  rw [integral_sub h₄_int hscale]
  rw [integral_const_mul]
  field_simp

end MathlibPlus.Analysis.Claim2312
