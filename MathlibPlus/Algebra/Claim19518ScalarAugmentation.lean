import Mathlib

namespace MathlibPlus.Algebra

/-- The scalar image of the literal contact tensor from admitted claim 19518. -/
def contactTensorScalar_claim19518
    {R A : Type*} [Ring R] [Ring A]
    (ε : R →+* A) (S T : R) (w : A) : A :=
  w * ε S + w * ε T

/-- The scalar image of the zipper tensor from admitted claim 19518. -/
def zipperTensorScalar_claim19518
    {R A : Type*} [Ring R] [Ring A]
    (ε : R →+* A) (S T : R) (w : A) : A :=
  ε S + (2 * w - 1) * ε T

end MathlibPlus.Algebra
