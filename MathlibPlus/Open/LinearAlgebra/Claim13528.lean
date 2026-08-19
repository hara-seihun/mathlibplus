import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim13528

/-- Every three-by-three matrix factoring through a two-dimensional middle
space has zero determinant. -/
def threeByTwoTwoByTwoTwoByThreeDeterminant : Prop :=
  ∀ {R : Type*} [CommRing R]
    (L : Matrix (Fin 3) (Fin 2) R)
    (B : Matrix (Fin 2) (Fin 2) R)
    (Rmat : Matrix (Fin 2) (Fin 3) R),
    Matrix.det (L * B * Rmat) = 0

end MathlibPlus.Open.LinearAlgebra.Claim13528
