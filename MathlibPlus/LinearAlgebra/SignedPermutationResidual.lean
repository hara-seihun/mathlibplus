import Mathlib

namespace MathlibPlus.LinearAlgebra.SignedPermutationResidual

/-- The four-row residual block displayed in the admitted claim. It is kept as
a generic matrix over a semiring so that the integer entries do not silently
choose an ambient scalar field. -/
def residualBlock {R : Type*} [Semiring R] : Matrix (Fin 4) (Fin 4) R :=
  !![72, 0, 0, 0;
      0, 72, 0, 0;
      0, 0, 0, 144;
      0, 0, 144, 0]

end MathlibPlus.LinearAlgebra.SignedPermutationResidual
