import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 4571: the mixed two-way coupling in a two-by-two square trace. -/
theorem squareTraceMixedWord (R : Type*) [CommRing R] (x a b y : R) :
    Matrix.trace ((!![x, a; b, y] : Matrix (Fin 2) (Fin 2) R) ^ 2) =
      x ^ 2 + y ^ 2 + 2 * a * b := by
  simp [Matrix.trace, pow_two, Fin.sum_univ_two]
  ring

end MathlibPlus.Algebra
