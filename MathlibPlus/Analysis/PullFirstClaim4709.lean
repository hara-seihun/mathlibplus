import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Analysis.Claim4709

/-- The positive-index theta tail from claim 4709. -/
noncomputable def thetaTail (u : ℝ) : ℝ :=
  ∑' m : ℕ,
    if 1 ≤ m then
      Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u))
    else 0

/-- The primitive theta moments from claim 4709.  The integral over `Ioi 0`
represents the displayed integral from zero to infinity. -/
noncomputable def primitiveThetaMoment (n : ℕ) : ℝ :=
  (2 : ℝ) / (Nat.factorial (2 * n) : ℝ) *
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2) * thetaTail u * u ^ (2 * n)

end MathlibPlus.Analysis.Claim4709
