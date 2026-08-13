import Mathlib

namespace MathlibPlus.Algebra

/-- The ordered-chamber substitution from admitted claim 851, with Lean's
zero-based indices corresponding to the source's indices 1 through 7. -/
theorem orderedChamberSubstitution_claim851
    (β y : Fin 7 → ℝ)
    (h01 : β 1 ≤ β 0)
    (h12 : β 2 ≤ β 1)
    (h23 : β 3 ≤ β 2)
    (h34 : β 4 ≤ β 3)
    (h45 : β 5 ≤ β 4)
    (h56 : β 6 ≤ β 5)
    (hy0 : y 0 = β 0 - β 1)
    (hy1 : y 1 = β 1 - β 2)
    (hy2 : y 2 = β 2 - β 3)
    (hy3 : y 3 = β 3 - β 4)
    (hy4 : y 4 = β 4 - β 5)
    (hy5 : y 5 = β 5 - β 6)
    (hy6 : y 6 = β 6)
    (hpos : 0 < β 6) :
    0 ≤ y 0 ∧
    0 ≤ y 1 ∧
    0 ≤ y 2 ∧
    0 ≤ y 3 ∧
    0 ≤ y 4 ∧
    0 ≤ y 5 ∧
    0 < y 6 ∧
    β 0 = y 0 + y 1 + y 2 + y 3 + y 4 + y 5 + y 6 ∧
    β 1 = y 1 + y 2 + y 3 + y 4 + y 5 + y 6 ∧
    β 2 = y 2 + y 3 + y 4 + y 5 + y 6 ∧
    β 3 = y 3 + y 4 + y 5 + y 6 ∧
    β 4 = y 4 + y 5 + y 6 ∧
    β 5 = y 5 + y 6 ∧
    β 6 = y 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith

end MathlibPlus.Algebra
