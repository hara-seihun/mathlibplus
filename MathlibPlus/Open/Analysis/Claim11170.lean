import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Exact complex zero locus of the dyadic exponential filter from claim
11170.  The multiplier is written with `Complex.exp` so the meaning of the
complex power `2^(-1/2-z)` is explicit. -/
def dyadicFilterZeroLocusClaim11170 : Prop :=
  let multiplier : ℂ → ℂ := fun z ↦
    1 - Complex.exp (-(1 / 2 + z) * (Real.log 2 : ℂ))
  (∀ z : ℂ,
      multiplier z = 0 ↔
        ∃ k : ℤ,
          z = -(1 / 2 : ℂ) +
            ((2 * Real.pi * (k : ℝ) / Real.log 2 : ℝ) : ℂ) * Complex.I) ∧
    (∀ z : ℂ, 0 ≤ z.re → multiplier z ≠ 0)

end MathlibPlus.Open.Analysis
