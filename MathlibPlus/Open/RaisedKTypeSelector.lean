import Mathlib

/-!
# Square-root bound for the least safe raised K-type selector

This open-registry node records admitted claim 306 from legacy packet `C-0019`.
The phase, safe-window polynomial, and leastness condition are inlined so the node
does not depend on definitions awaiting admission in separate submissions.
-/

open scoped BigOperators

namespace MathlibPlus.Open.RaisedKType

/-- For every positive real weight, the least selector whose total phase lies in the
safe window grows at most on the square-root scale as the height tends to either
infinity. The existential function is constrained by `IsLeast`, so existence and
leastness are not hidden by a default value for an empty set. -/
def leastSelectorSquareRootUpperBound : Prop :=
  ∀ k : ℝ, 0 < k →
    let safe : ℝ → ℕ → Prop := fun t m =>
      let theta := t * Real.log 2 + ∑ r ∈ Finset.range m,
        (Real.arctan (t / (k + 2 * (r : ℝ) + 1 / 2)) +
          Real.arctan (t / (k + 2 * (r : ℝ) + 3 / 2)))
      0 ≤ 73 * (Real.cos theta ^ 2) ^ 2 - 68 * Real.cos theta ^ 2 + 4
    ∃ mStar : ℝ → ℕ,
      (∀ t : ℝ, IsLeast {m : ℕ | safe t m} (mStar t)) ∧
      (fun t : ℝ ↦ (mStar t : ℝ)) =O[Filter.cocompact ℝ]
        (fun t : ℝ ↦ Real.sqrt |t| + 1)

end MathlibPlus.Open.RaisedKType
