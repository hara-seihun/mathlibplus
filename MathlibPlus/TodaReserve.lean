import Mathlib

/-!
# Determinant reserve from logarithmic curvature

The exact scalar consequence of condensation and logarithmic curvature in Record 8
of legacy packet `C-0231`.
-/

namespace MathlibPlus.TodaReserve

/-- A Desnanot--Jacobi condensation identity converts the adjacent determinant ratio
into one minus the exponential of negative logarithmic curvature. -/
theorem reserveFromLogCurvature
    (dPlus dMinus d dPrev dNext : ℝ)
    (hdPrev : 0 < dPrev) (hd : 0 < d) (hdNext : 0 < dNext)
    (hcond : dPlus * dMinus = d ^ 2 - dPrev * dNext) :
    dPlus * dMinus / d ^ 2 =
      1 - Real.exp (-Real.log (d ^ 2 / (dPrev * dNext))) := by
  have hdSq : d ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hd)
  have hprod : dPrev * dNext ≠ 0 :=
    mul_ne_zero (ne_of_gt hdPrev) (ne_of_gt hdNext)
  have hratio : 0 < d ^ 2 / (dPrev * dNext) :=
    div_pos (sq_pos_of_pos hd) (mul_pos hdPrev hdNext)
  rw [Real.exp_neg, Real.exp_log hratio]
  rw [hcond]
  field_simp

end MathlibPlus.TodaReserve
