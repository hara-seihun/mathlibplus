import Mathlib

/-!
# Two-mode exterior-square identity

The two-mode quadratic identity from admitted claim 4190 is an exact
commutative-ring calculation; no positivity or nonvanishing assumptions are
needed.
-/

namespace MathlibPlus.Algebra

/-- The self-pair terms cancel in the two-mode exterior-square expression. -/
theorem twoModeExteriorSquare {R : Type*} [CommRing R] (u v b c : R) :
    (u + v) * (b ^ 2 * u + c ^ 2 * v) - (b * u + c * v) ^ 2 =
      u * v * (b - c) ^ 2 := by
  ring

end MathlibPlus.Algebra
