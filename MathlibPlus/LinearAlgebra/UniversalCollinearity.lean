import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- Claim 25061: a rational affine collinearity relation between three
 two-coordinate states forces the displayed determinant to vanish. -/
theorem universalCollinearityDeterminant (E F G : Fin 2 → ℚ) (q : ℚ)
    (h : G - E = q • (F - E)) :
    Matrix.det
      (!![(F - E) 0, (F - E) 1; (G - E) 0, (G - E) 1] :
        Matrix (Fin 2) (Fin 2) ℚ) = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.sub_apply, Pi.smul_apply] at h0 h1
  simp [Matrix.det_fin_two]
  rw [h0, h1]
  ring

end MathlibPlus.LinearAlgebra
