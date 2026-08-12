import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory

/-! Formalization of admitted claim 18363 (R-0154). -/

/-- Positive complementary factors have constant inverse-square-root weight and
additive logarithmic weight. -/
theorem complementaryDivisorWeightAndLog_claim18363
    (d e R : ℝ) (hd : 0 < d) (he : 0 < e) (_hR : 0 < R)
    (hde : d * e = R) :
    (Real.sqrt d)⁻¹ * (Real.sqrt e)⁻¹ = (Real.sqrt R)⁻¹ ∧
      Real.log d + Real.log e = Real.log R := by
  have hmul : Real.sqrt d * Real.sqrt e = Real.sqrt R := by
    rw [← Real.sqrt_mul (le_of_lt hd), hde]
  constructor
  · calc
      (Real.sqrt d)⁻¹ * (Real.sqrt e)⁻¹ =
          (Real.sqrt e * Real.sqrt d)⁻¹ := by
            rw [mul_inv_rev]
      _ = (Real.sqrt d * Real.sqrt e)⁻¹ := by rw [mul_comm]
      _ = (Real.sqrt R)⁻¹ := by rw [hmul]
  · rw [← Real.log_mul (ne_of_gt hd) (ne_of_gt he), hde]

end MathlibPlus.NumberTheory
