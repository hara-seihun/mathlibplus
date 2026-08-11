import Mathlib

namespace MathlibPlus.LinearAlgebra.ProjectiveRowDifference

/-- Claim 15718: exact projective row-difference identity for a nonzero pivot. -/
theorem exactThreeByThreeProjectiveRowDifference
    (f₁₁ f₁₂ f₁₃ f₂₁ f₂₂ f₂₃ f₃₁ f₃₂ f₃₃ : ℝ)
    (h₂₁ : f₂₁ ≠ 0) :
    Matrix.det (!![f₁₁, f₁₂, f₁₃; f₂₁, f₂₂, f₂₃; f₃₁, f₃₂, f₃₃]) =
      (1 / f₂₁) * Matrix.det
        (!![f₁₁ * f₂₂ - f₁₂ * f₂₁, f₁₁ * f₂₃ - f₁₃ * f₂₁;
            f₂₁ * f₃₂ - f₂₂ * f₃₁, f₂₁ * f₃₃ - f₂₃ * f₃₁]) := by
  simp [Matrix.det_fin_three, Matrix.det_fin_two]
  field_simp [h₂₁]
  ring

end MathlibPlus.LinearAlgebra.ProjectiveRowDifference
