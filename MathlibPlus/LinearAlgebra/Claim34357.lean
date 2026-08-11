import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim34357

/-- Claim 34357: the Plücker relation for the six defects, represented as
negatives of the six 2-by-2 minors of an arbitrary two-row rooted-column table.
The packet does not define a separate rooted-piece type, so the rooted columns
are left as arbitrary entries of a commutative ring. -/
theorem rootedColumnPlucker {R : Type*} [CommRing R]
    (a0 a1 b0 b1 c0 c1 d0 d1 : R) :
    let Δ01 := -(a0 * b1 - a1 * b0)
    let Δ02 := -(a0 * c1 - a1 * c0)
    let Δ03 := -(a0 * d1 - a1 * d0)
    let Δ12 := -(b0 * c1 - b1 * c0)
    let Δ13 := -(b0 * d1 - b1 * d0)
    let Δ23 := -(c0 * d1 - c1 * d0)
    Δ01 * Δ23 - Δ02 * Δ13 + Δ03 * Δ12 = 0 := by
  dsimp
  ring

end MathlibPlus.LinearAlgebra.Claim34357
