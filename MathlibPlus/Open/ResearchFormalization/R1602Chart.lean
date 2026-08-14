import Mathlib

namespace MathlibPlus.Open

abbrev F3 := ZMod 3

/-- Coordinates for the displayed quotient chart in Claim 39533. -/
structure F3Four where
  z : F3
  w : F3
  x : F3
  y : F3

/-- The displayed nonlinear quotient formula, with its carry left arbitrary. -/
def nonlinearQuotientChart (t : F3 → F3 → F3 → F3) (p : F3Four) : F3Four :=
  { z := p.z + t p.w p.x p.y
    w := p.w + if p.x = 0 ∧ p.y = 2 then (1 : F3) else 0
    x := p.x
    y := p.y + if p.x = 2 then (1 : F3) else 0 }

/--
Claim 39533.  The fixed nonlinear quotient chart has coordinates
`(z,w,x,y) ∈ 𝔽₃⁴`, the displayed permutation formula, and a top carry
` t : 𝔽₃³ → 𝔽₃` vanishing at zero.
-/
def fixedNonlinearQuotientChart
    (t : F3 → F3 → F3 → F3) : Prop :=
  t 0 0 0 = 0 ∧ Function.Bijective (nonlinearQuotientChart t)

end MathlibPlus.Open
