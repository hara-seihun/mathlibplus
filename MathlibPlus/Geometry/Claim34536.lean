import Mathlib

namespace MathlibPlus.Geometry

/-- The numerical exceptional-set consequence recorded in claim 34536.

The predecessor cardinality estimate for `B` is an explicit hypothesis: it is
claim 34534's `|B| ≤ 5 (c + b + 5 E)` input to the final budget calculation. -/
theorem hullBasedLinearExceptionalBound_claim34536
    {α : Type*} [DecidableEq α]
    (B : Finset α) (b E c h : ℕ)
    (hc : 1 ≤ c)
    (hbudget : b + E + 4 * c - 4 ≤ 2 * h)
    (hB : B.card ≤ 5 * (c + b + 5 * E)) :
    c + b + 5 * E ≤ 10 * h + 1 ∧ B.card ≤ 50 * h + 5 := by
  omega

end MathlibPlus.Geometry
