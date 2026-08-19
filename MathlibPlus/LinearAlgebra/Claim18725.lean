import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim18725

/-- Top exterior-coordinate (determinant) form of the degree-N homogeneity
statement. -/
theorem determinant_homogeneity
    {R : Type*} [CommRing R] (N : ℕ) (scale : R)
    (A : Matrix (Fin N) (Fin N) R) :
    (scale • A).det = scale ^ N * A.det := by
  simpa using Matrix.det_smul A scale

end MathlibPlus.LinearAlgebra.Claim18725
