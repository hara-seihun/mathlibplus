import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim21328IntervalSplit

def intervalSplitSupport (L : ℤ) : Set (ℤ × ℤ) :=
  {p | ∃ i : ℤ, 1 ≤ i ∧ i < L ∧
    p = (min i 3, min (L - i) 3)}

/-- Claim 21328: once the interval has length six, the capped split support
is exactly the five displayed ordered pairs. -/
def claim21328_intervalSplitSupportSaturates : Prop :=
  ∀ L : ℤ, 6 ≤ L →
    intervalSplitSupport L =
      {(1, 3), (2, 3), (3, 3), (3, 2), (3, 1)}

end MathlibPlus.Open.Combinatorics.Claim21328IntervalSplit
