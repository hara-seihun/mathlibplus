import Mathlib.Tactic

namespace MathlibPlus.NumberTheory

/-- The exact numerical Satake fixture in admitted claim 12964.  The three
quantities called the second power trace, degree-two Euler coefficient, and
square of the first coefficient are 13, 19, and 25 respectively, so they are
pairwise distinct. -/
theorem claim12964_satakeCoefficientSeparation :
    let α : ℚ := 2
    let β : ℚ := 3
    (α ^ 2 + β ^ 2 = 13) ∧
      (α ^ 2 + α * β + β ^ 2 = 19) ∧
      ((α + β) ^ 2 = 25) ∧
      (α ^ 2 + β ^ 2 ≠ α ^ 2 + α * β + β ^ 2) ∧
      (α ^ 2 + α * β + β ^ 2 ≠ (α + β) ^ 2) ∧
      (α ^ 2 + β ^ 2 ≠ (α + β) ^ 2) := by
  norm_num

end MathlibPlus.NumberTheory
