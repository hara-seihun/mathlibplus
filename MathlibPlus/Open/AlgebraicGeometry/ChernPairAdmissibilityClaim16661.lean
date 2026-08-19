import Mathlib

namespace MathlibPlus.Open.AlgebraicGeometry

/-- Claim 16661: the displayed integer Chern coordinates satisfy precisely the
four numerical geography conditions recorded in the source packet. -/
def c1Sq_c2_admissible_claim16661 : Prop :=
  let c1Sq : ℤ := 1
  let c2 : ℤ := 11
  c1Sq > 0 ∧
    c2 > 0 ∧
    5 * c1Sq ≥ c2 - 36 ∧
    c1Sq ≤ 3 * c2 ∧
    12 ∣ c1Sq + c2

end MathlibPlus.Open.AlgebraicGeometry
