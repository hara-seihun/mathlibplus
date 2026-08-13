import Mathlib

namespace MathlibPlus.Algebra

/--
The pointwise Jacobi transfer identity from admitted claim 8997.  The
suppressed indices `j,N` are represented by arbitrary real values at the two
neighboring sites and at the current site.
-/
theorem twoByTwoJacobiTransfer_claim8997
    (aPrev aNext vPrev v vNext lambda : ℝ)
    (_haPrev : 0 < aPrev) (haNext : 0 < aNext)
    (h : aPrev * vPrev + aNext * vNext = lambda * v) :
    ![vNext, v] =
      Matrix.mulVec
        (!![lambda / aNext, -aPrev / aNext; (1 : ℝ), 0] :
          Matrix (Fin 2) (Fin 2) ℝ) ![v, vPrev] := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec]
    field_simp
    linarith
  · simp [Matrix.mulVec]

end MathlibPlus.Algebra
