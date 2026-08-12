import Mathlib

namespace MathlibPlus.NumberTheory

/--
The reciprocal-root arithmetic and quadratic factorization from admitted claim
4558.  The source's `P_-` is inlined as `1 + 7 * u + 9 * u ^ 2`, so this
statement introduces no detached polynomial definition.
-/
theorem reciprocalRoots_claim4558 :
    let α : ℝ := (-7 + Real.sqrt 13) / 2
    let β : ℝ := (-7 - Real.sqrt 13) / 2
    α + β = -7 ∧
      α * β = 9 ∧
      ∀ u : ℝ, 1 + 7 * u + 9 * u ^ 2 =
        (1 - α * u) * (1 - β * u) := by
  dsimp
  have hs : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := by
    rw [Real.sq_sqrt]
    norm_num
  constructor
  · ring
  constructor
  · nlinarith
  · intro u
    nlinarith

end MathlibPlus.NumberTheory
