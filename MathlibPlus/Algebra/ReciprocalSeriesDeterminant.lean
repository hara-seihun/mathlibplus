import MathlibPlus.Open.Algebra.Claim19222
import MathlibPlus.Open.Algebra.ReciprocalShiftedHankel

namespace MathlibPlus.Algebra

<<<<<<< ours
/-- The explicit-inverse and canonical-inverse formulations of the reciprocal
shifted-Hankel determinant identity are equivalent. -/
theorem reciprocalSeriesDeterminant_iff_reciprocalShiftedHankel :
    MathlibPlus.Open.Algebra.reciprocalSeriesDeterminant_claim19222.{u} ↔
      MathlibPlus.Open.Algebra.reciprocalShiftedHankelDeterminantIdentity.{u} := by
  constructor
  · intro h R _ N H hH
    have hH' : PowerSeries.constantCoeff H ≠ 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hH
    have hdet := h R H H⁻¹ hH' (PowerSeries.mul_inv_cancel H hH') N
    dsimp
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hdet
  · intro h K _ H B hH hmul N
    have hH' : PowerSeries.constantCoeff H ≠ 0 := hH
    have hmul' : B * H = 1 := by
      simpa [mul_comm] using hmul
    have hB : B = H⁻¹ :=
      (PowerSeries.eq_inv_iff_mul_eq_one hH').2 hmul'
    have hcoeff : PowerSeries.coeff 0 H ≠ 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hH
    have hdet := h K N H hcoeff
    dsimp at hdet
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB] using hdet
=======
universe u

/-- The explicit-reciprocal and canonical-inverse formulations of the shifted
Hankel determinant identity are equivalent. -/
theorem reciprocalSeriesDeterminant_iff_reciprocalShiftedHankel :
    MathlibPlus.Open.Algebra.reciprocalSeriesDeterminant_claim19222.{u} ↔
      MathlibPlus.Open.Algebra.reciprocalShiftedHankelDeterminantIdentity.{u} := by
  unfold MathlibPlus.Open.Algebra.reciprocalSeriesDeterminant_claim19222
    MathlibPlus.Open.Algebra.reciprocalShiftedHankelDeterminantIdentity
  constructor
  · intro h R _ N H h0
    let B : PowerSeries R := H⁻¹
    have h0' : PowerSeries.constantCoeff H ≠ 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    have hHB : H * B = 1 := by
      dsimp [B]
      exact PowerSeries.mul_inv_cancel H h0'
    have hh := h R H B h0' hHB N
    simpa [B] using hh
  · intro h K _ H B h0 hHB N
    have h0' : PowerSeries.constantCoeff H ≠ 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    have hBinv : B = H⁻¹ := by
      apply (PowerSeries.eq_inv_iff_mul_eq_one h0').2
      simpa [mul_comm] using hHB
    subst B
    have h0coeff : PowerSeries.coeff 0 H ≠ 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    have hh := h K N H h0coeff
    simpa using hh
>>>>>>> theirs

end MathlibPlus.Algebra
