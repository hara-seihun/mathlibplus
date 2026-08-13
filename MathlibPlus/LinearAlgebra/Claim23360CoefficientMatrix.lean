import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- The displayed coefficient matrix from claim 23360 cannot be a scalar
multiple of the all-ones rank-one tensor. This is the entrywise equivalent
form of the rank-two versus rank-at-most-one obstruction. -/
theorem coefficient_matrix_not_scalar_square_claim23360
    {R : Type*} [Ring R] [Nontrivial R] (scalar : R) :
    ¬ ((!![0, 1; 1, 2] : Matrix (Fin 2) (Fin 2) R) =
      scalar • (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) R)) := by
  intro h
  have h00 : (0 : R) = scalar := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) h
  have h01 : (1 : R) = scalar := by
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) h
  exact (zero_ne_one : (0 : R) ≠ 1) (h00.trans h01.symm)

end MathlibPlus.LinearAlgebra
