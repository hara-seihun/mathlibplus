import MathlibPlus.Open.Algebra.Claim19222
import MathlibPlus.Open.Algebra.ReciprocalShiftedHankel

namespace MathlibPlus.Algebra

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

end MathlibPlus.Algebra
