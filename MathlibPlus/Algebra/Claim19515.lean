import Mathlib

namespace MathlibPlus.Algebra.Claim19515

/-- The proposed zipper tensor, with the coefficient variable acting in a
module over the coefficient ring. -/
def zipperTensor {R M : Type*} [Ring R] [AddCommMonoid M]
    [Module R M] (w : R) (S T : M) : M :=
  S + (((2 : R) * w) - 1) • T

theorem zipperTensor_eq {R M : Type*} [Ring R] [AddCommMonoid M]
    [Module R M] (w : R) (S T : M) :
    zipperTensor w S T = S + (((2 : R) * w) - 1) • T := by
  rfl

end MathlibPlus.Algebra.Claim19515
