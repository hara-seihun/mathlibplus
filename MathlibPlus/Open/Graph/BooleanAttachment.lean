import Mathlib

namespace MathlibPlus.Open.Graph

/-- The first Boolean attachment invariant from Claim 22841. -/
def c1 (x : Fin 7 → ZMod 2) : ZMod 2 :=
  (x 3 + x 4) * (x 5 + x 6)

/-- The second Boolean attachment invariant from Claim 22841. -/
def c2 (x : Fin 7 → ZMod 2) : ZMod 2 :=
  x 3 * x 5 + x 4 * x 5 + x 3 * x 4 * x 5 +
    x 3 * x 4 * x 6 + x 5 * x 6 + x 3 * x 5 * x 6 +
    x 4 * x 5 * x 6

end MathlibPlus.Open.Graph
