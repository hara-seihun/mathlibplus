import Mathlib

namespace MathlibPlus.Combinatorics.OuterMaskCount

/--
RECEIPT carrier for Claim 39883: after the affine position is fixed, an outer
mask is exactly a two-element subset of the remaining seven positions.
-/
def exactOuterMaskCount : Prop :=
  Fintype.card {s : Finset (Fin 7) // s.card = 2} = 21

end MathlibPlus.Combinatorics.OuterMaskCount
