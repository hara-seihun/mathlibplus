import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Directed logarithm upper bound at the fixed scale `2^56`. -/
def directedLogarithmUpperBound1210 : Prop :=
  ∀ (p u z : ℝ),
    0 < u →
    0 ≤ z →
    z < (1 : ℝ) / 100000 →
    u ≤ p →
    p < u * (1 + (1 : ℝ) / 100000) →
    z = (p - u) / u →
    let S : ℝ := (2 : ℝ) ^ 56
    let Z : ℤ := Int.ceil (S * z)
    let Lu : ℤ := Int.ceil (S * Real.log u)
    let Λ : ℤ :=
      Lu + Z - Int.floor (((Z : ℝ) ^ 2) / (2 * S)) +
        Int.ceil (((Z : ℝ) ^ 3) / (3 * S ^ 2))
    Real.log p ≤ (Λ : ℝ) / S

end MathlibPlus.Open.Analysis
