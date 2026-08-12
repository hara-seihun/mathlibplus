import Mathlib

namespace MathlibPlus.Algebra.Claim25145

open Polynomial

/-- Resultant row addition, with the monic degree hypotheses retained from
claim 25145.  The algebraic identity itself only needs the displayed bound on
`F`. -/
theorem resultant_row_operation_claim25145
    {R : Type*} [CommRing R]
    (F G : R[X]) (m : ℕ)
    (hFmonic : F.Monic) (hGmonic : G.Monic)
    (hFdegree : F.natDegree = m) (hGdegree : G.natDegree = m) :
    resultant F G m m = (-1 : R) ^ m * resultant F (F - G) m m := by
  have hFle : F.natDegree ≤ m := by omega
  have hshift := resultant_add_mul_right F (-G) 1 m m (by simp) hFle
  have hshift' : resultant F (F - G) m m = resultant F (-G) m m := by
    rw [show (-G + F * 1 : R[X]) = F - G by
      simp only [mul_one, sub_eq_add_neg, add_comm]] at hshift
    exact hshift
  have hneg : resultant F (-G) m m =
      (-1 : R) ^ m * resultant F G m m := by
    have hneg' := resultant_C_mul_right F G m m (-1 : R)
    rw [show (Polynomial.C (-1 : R) * G : R[X]) = -G by
      simp [Polynomial.C_neg]] at hneg'
    exact hneg'
  have hsub : resultant F (F - G) m m =
      (-1 : R) ^ m * resultant F G m m := hshift'.trans hneg
  have hs : (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    resultant F G m m = 1 * resultant F G m m := by simp
    _ = ((-1 : R) ^ m * (-1 : R) ^ m) * resultant F G m m := by rw [hs]
    _ = (-1 : R) ^ m * ((-1 : R) ^ m * resultant F G m m) := by ring
    _ = (-1 : R) ^ m * resultant F (F - G) m m := by rw [← hsub]

end MathlibPlus.Algebra.Claim25145
