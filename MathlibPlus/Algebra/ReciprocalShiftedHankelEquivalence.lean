import MathlibPlus.Open.Algebra.Claim19222
import MathlibPlus.Open.Algebra.ReciprocalShiftedHankel

namespace MathlibPlus.Algebra

universe u

/-- The two independently registered reciprocal shifted-Hankel determinant
identities differ only in whether the reciprocal series is quantified together
with an explicit inverse equation or written as `H⁻¹`. -/
theorem reciprocalSeriesDeterminant_iff_reciprocalShiftedHankel :
    MathlibPlus.Open.Algebra.reciprocalSeriesDeterminant_claim19222.{u} ↔
      MathlibPlus.Open.Algebra.reciprocalShiftedHankelDeterminantIdentity.{u} := by
  constructor
  · intro hExplicit R _ N H hH
    have hH' : PowerSeries.constantCoeff H ≠ 0 := by
      simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hH
    have hInv : H * H⁻¹ = (1 : PowerSeries R) := by
      rw [mul_comm]
      exact (PowerSeries.eq_inv_iff_mul_eq_one hH').1 rfl
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      hExplicit R H H⁻¹ hH' hInv N
  · intro hCanonical R _ H B hH hHB N
    have hB : B = H⁻¹ := by
      apply (PowerSeries.eq_inv_iff_mul_eq_one hH).2
      simpa [mul_comm] using hHB
    subst B
    have hH' : PowerSeries.coeff 0 H ≠ 0 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hH
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      hCanonical R N H hH'

end MathlibPlus.Algebra
