import Mathlib

namespace MathlibPlus.Analysis.Claim1972

/-- The exact derivative identity for the logarithmic Vinogradov--Korobov scale.
The source claim's separate strict-concavity conclusion is left as an explicit
boundary; this theorem captures its displayed derivative calculation on the
full natural domain `L > 1`. -/
theorem vkScale_derivative_claim1972 {L : ℝ} (hL : 1 < L) :
    deriv
        (fun x : ℝ => Real.rpow x (2 / 3 : ℝ) *
          Real.rpow (Real.log x) (1 / 3 : ℝ)) L =
      (2 / 3 : ℝ) * Real.rpow L ((2 / 3 : ℝ) - 1) *
          Real.rpow (Real.log L) (1 / 3 : ℝ) +
        Real.rpow L (2 / 3 : ℝ) *
          (L⁻¹ * (1 / 3 : ℝ) *
            Real.rpow (Real.log L) ((1 / 3 : ℝ) - 1)) := by
  have hL0 : L ≠ 0 := by linarith
  have hw : Real.log L ≠ 0 := (Real.log_pos hL).ne'
  have h₁ : HasDerivAt (fun x : ℝ => Real.rpow x (2 / 3 : ℝ))
      ((2 / 3 : ℝ) * Real.rpow L ((2 / 3 : ℝ) - 1)) L := by
    convert (hasDerivAt_id L).rpow_const (p := (2 / 3 : ℝ))
      (Or.inl hL0) using 1 <;> simp
  have h₂ : HasDerivAt (fun x : ℝ => Real.rpow (Real.log x) (1 / 3 : ℝ))
      (L⁻¹ * (1 / 3 : ℝ) * Real.rpow (Real.log L) ((1 / 3 : ℝ) - 1)) L := by
    exact (Real.hasDerivAt_log hL0).rpow_const (Or.inl hw)
  exact (h₁.mul h₂).deriv

end MathlibPlus.Analysis.Claim1972
