import Mathlib

namespace MathlibPlus.Open

/-- The differential ratio of the scalar sequence at a nonzero preceding index. -/
def differentialRatio
    (K : Type*) [Field K] (q : Kˣ) (r lambda : ℕ → K) : Prop :=
  ∀ n : ℕ, n ≥ 1 → r (n - 1) ≠ 0 →
    lambda n = r n / ((q : K) * r (n - 1))

end MathlibPlus.Open
