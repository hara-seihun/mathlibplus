import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1120

abbrev F7 := ZMod 7

def adjacentDifference
    (p q : Equiv.Perm F7) (u x : F7) : F7 :=
  p.symm (p (x + 2 * u) - 2 * q u)

/-- Claim 29132: the common-sign adjacent equation with its displayed
pullback difference map. -/
def commonSignAdjacentEquation
    (p q : Equiv.Perm F7) (a e t : F7 → F7) : Prop :=
  ∀ (u x : F7),
    t (adjacentDifference p q u x) - t x =
      a (x + 2 * u) - a (adjacentDifference p q u x) - 2 * e u

end MathlibPlus.Open.ResearchFormalization.R1120
