import Mathlib

namespace MathlibPlus.Algebra.GrassmannPlucker

/-- Claim 6696: the rank-two Grassmann--Plücker relation for four columns.

The source calls the inputs rooted columns but does not define that restriction.
The displayed algebraic identity is therefore stated for arbitrary four columns;
this makes the scope explicit rather than silently introducing a root hypothesis. -/
theorem rankTwoGrassmannPlucker (R : Type*) [CommRing R]
    (col : Fin 4 → Fin 2 → R) :
    let Δ : Fin 4 → Fin 4 → R :=
      fun i j => col i 0 * col j 1 - col i 1 * col j 0
    Δ 0 1 * Δ 2 3 - Δ 0 2 * Δ 1 3 + Δ 0 3 * Δ 1 2 = 0 := by
  dsimp
  ring

end MathlibPlus.Algebra.GrassmannPlucker
