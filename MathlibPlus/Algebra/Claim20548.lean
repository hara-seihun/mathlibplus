import Mathlib

namespace MathlibPlus.Algebra.Claim20548

/--
The three-root Möbius interaction from claim 20548, after writing every
nonempty `u_S` coordinate as `y_S - y_∅` in the original cell coordinates.
-/
theorem h3_originalCellVariables_claim20548 {R : Type*} [Ring R]
    (y0 y1 y2 y3 y12 y13 y23 y123 : R) :
    let u1 := y1 - y0
    let u2 := y2 - y0
    let u3 := y3 - y0
    let u12 := y12 - y0
    let u13 := y13 - y0
    let u23 := y23 - y0
    let u123 := y123 - y0
    u1 + u2 + u3 - u12 - u13 - u23 + u123
      = -y0 + y1 + y2 + y3 - y12 - y13 - y23 + y123 := by
  dsimp
  abel

end MathlibPlus.Algebra.Claim20548
