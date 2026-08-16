import Mathlib

/-!
# Algebraic moment-geometry witnesses

Two exact algebraic identities extracted from source record `C-0010`. This file
formalizes neither the packet's measure-rigidity classification nor its abstract
exterior-positivity obstruction.
-/

namespace MathlibPlus.MomentGeometry

/-- Exact final-Hankel defect for two atoms, before imposing positivity of their
weights or locations. -/
theorem twoPositiveAtomDefect (w₁ w₂ z₁ z₂ : ℝ) :
    w₁ * z₁ ^ 3 * (w₁ * z₁ ^ 5) +
        w₁ * z₁ ^ 3 * (w₂ * z₂ ^ 5) +
        w₂ * z₂ ^ 3 * (w₁ * z₁ ^ 5) +
        w₂ * z₂ ^ 3 * (w₂ * z₂ ^ 5) -
      (w₁ * z₁ ^ 4 + w₂ * z₂ ^ 4) ^ 2 =
    w₁ * w₂ * z₁ ^ 3 * z₂ ^ 3 * (z₁ - z₂) ^ 2 := by
  ring

/-- Rank-two Bezout expression in the first four column sums of a weighted power
matrix. -/
def rankTwoColumnSumExpression (h₀ h₁ h₂ h₃ : ℝ) : ℝ :=
  h₀ * (3 * h₀ * h₁ * h₃ - 4 * h₀ * h₂ ^ 2 + h₁ ^ 2 * h₂)

/-- Exact negative value of the packet's three-atom column-sum witness. -/
theorem threeAtomExteriorWitness :
    rankTwoColumnSumExpression 7 33 185 1089 = -15106 := by
  norm_num [rankTwoColumnSumExpression]

end MathlibPlus.MomentGeometry
