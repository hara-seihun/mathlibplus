import Mathlib

/-!
# Binary pair-state endpoint products

Statement-faithful formalizations of admitted claims 24951--24954 from packet
`R-0812`.  The surrounding claim works over a UFD and defines
`α = c + d - a - b` and `β = c * d - a * b`; those hypotheses and definitions
are retained here rather than inferred from the displayed identities alone.
-/

namespace MathlibPlus.Algebra.PairState

/-- At the first endpoint, `β - aα = (c-a)(d-a)` (admitted claim 24951). -/
theorem endpointProductAtA {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (a b c d : R) :
    let α := c + d - a - b
    let β := c * d - a * b
    β - a * α = (c - a) * (d - a) := by
  dsimp
  ring

/-- At the second endpoint, `β - bα = (c-b)(d-b)` (admitted claim 24952). -/
theorem endpointProductAtB {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (a b c d : R) :
    let α := c + d - a - b
    let β := c * d - a * b
    β - b * α = (c - b) * (d - b) := by
  dsimp
  ring

/-- At the third endpoint, `β - cα = -(a-c)(b-c)` (admitted claim 24953). -/
theorem endpointProductAtC {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (a b c d : R) :
    let α := c + d - a - b
    let β := c * d - a * b
    β - c * α = -(a - c) * (b - c) := by
  dsimp
  ring

/-- At the fourth endpoint, `β - dα = -(a-d)(b-d)` (admitted claim 24954). -/
theorem endpointProductAtD {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (a b c d : R) :
    let α := c + d - a - b
    let β := c * d - a * b
    β - d * α = -(a - d) * (b - d) := by
  dsimp
  ring

end MathlibPlus.Algebra.PairState
