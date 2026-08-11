import Mathlib

namespace MathlibPlus.AnalyticNumberTheory.ReciprocalXi

/-- Once the derivative-Hankel determinant has the stated orientation sign, the
orientation prefactor cancels it exactly. -/
theorem orientedCancellation_of_detIdentity (n : ℕ) (derivativeDet momentDet : ℂ)
    (h : derivativeDet =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * momentDet) :
    (-1 : ℂ) ^ (n * (n - 1) / 2) * derivativeDet = momentDet := by
  rw [h, ← mul_assoc, ← mul_pow]
  norm_num

end MathlibPlus.AnalyticNumberTheory.ReciprocalXi
