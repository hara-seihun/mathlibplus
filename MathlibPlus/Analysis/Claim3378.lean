import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Analysis.Claim3378

noncomputable section

/-- The primitive completed-theta sum over positive integer indices. -/
def primitiveCompletedTheta (u : ℝ) : ℝ :=
  ∑' q : {q : ℕ // 1 ≤ q},
    Real.exp (-Real.pi * (q.1 : ℝ) ^ 2 * Real.exp (2 * u))

/-- The completed-theta moment displayed in Claim 3378. -/
def primitiveCompletedThetaMoment (n : ℕ) : ℝ :=
  (2 : ℝ) / (Nat.factorial (2 * n) : ℝ) *
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2) * primitiveCompletedTheta u * u ^ (2 * n)

end

end MathlibPlus.Analysis.Claim3378
