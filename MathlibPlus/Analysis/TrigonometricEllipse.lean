import Mathlib

namespace MathlibPlus.Analysis.TrigonometricEllipse

/-- Claim 18003: the coefficient ellipse identity. -/
theorem coefficientEllipseIdentity {A B θ : ℝ}
    (hB : B = Real.cos θ)
    (hA : Real.sqrt 2 * A = Real.sin θ) :
    B ^ 2 + 2 * A ^ 2 = 1 := by
  have hsqrt : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    norm_num
  have hA_sq : (Real.sqrt (2 : ℝ) * A) ^ 2 = (Real.sin θ) ^ 2 :=
    congrArg (fun t : ℝ => t ^ 2) hA
  rw [hB]
  nlinarith [Real.sin_sq_add_cos_sq θ]

end MathlibPlus.Analysis.TrigonometricEllipse
