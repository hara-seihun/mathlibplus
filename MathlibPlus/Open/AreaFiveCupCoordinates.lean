import Mathlib

namespace MathlibPlus.Open

/--
The seven area-five cup-coordinate linear combinations, with the `H` and
`alpha` coordinates named explicitly.
-/
def areaFiveCupCoordinateLinearCombinations
    {R : Type*} [AddCommGroup R]
    (H0 H1 H2 H3 H4 H5 H11 H21 H22 H31 H32 H41 H111 H211 H221 H311 H1111 H2111 H11111 : R)
    (alpha5 alpha41 alpha32 alpha311 alpha221 alpha2111 alpha11111 : R) : Prop :=
  alpha5 = H0 - H1 + H2 - H3 + H4 - H5 ∧
  alpha41 = 2 • H0 - H1 + H2 + H11 - H3 - H21 + H4 + H31 - H41 ∧
  alpha32 = 2 • H0 - 2 • H1 + H2 + 2 • H11 - H3 - H21 + H31 + H22 - H32 ∧
  alpha311 = 3 • H0 - H1 + H2 + H11 - H3 - H21 - H111 + H31 + H211 - H311 ∧
  alpha221 = 2 • H0 - 2 • H1 + 2 • H2 + H11 - H21 - H111 + H22 + H211 - H221 ∧
  alpha2111 = 2 • H0 - H1 + H2 + H11 - H21 - H111 + H211 + H1111 - H2111 ∧
  alpha11111 = H0 - H1 + H11 - H111 + H1111 - H11111

end MathlibPlus.Open
