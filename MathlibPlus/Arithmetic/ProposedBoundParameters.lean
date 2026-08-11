import Mathlib

/-!
# Proposed-bound parameter arithmetic

The exact rational arithmetic recorded in admitted claim 20229 (locator
`R-0348`) is formalized here independently of the packet's analytic claim.
The source does not state a number type for the displayed parameters; `ℚ`
is used so that the terminating decimal is represented exactly.
-/

namespace MathlibPlus.Arithmetic

/-- The parameter identity and the stated one-hundredth gap to `1729/10000`. -/
theorem proposedBoundParameterIdentity :
    let t₀ : ℚ := 1579 / 10000
    let y₀ : ℚ := 1 / 10
    t₀ + y₀ ^ 2 / 2 = 1629 / 10000 ∧
      t₀ + y₀ ^ 2 / 2 = 0.1629 ∧
      1729 / 10000 - (t₀ + y₀ ^ 2 / 2) = 1 / 100 := by
  norm_num

end MathlibPlus.Arithmetic
