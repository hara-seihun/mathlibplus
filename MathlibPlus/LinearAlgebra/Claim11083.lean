import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim11083

/-- At `N = 8`, the diagonal Jacobian with entries `1, ..., N` has the
factorial determinant reported in claim 11083.  The ghost-coordinate map is a
source interface; this declaration retains its concrete Jacobian consequence. -/
theorem eightGhostJacobianDet :
    Matrix.det (Matrix.diagonal (fun i : Fin 8 => (i.1 + 1 : ℤ))) = 40320 := by
  rw [Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

end MathlibPlus.LinearAlgebra.Claim11083
