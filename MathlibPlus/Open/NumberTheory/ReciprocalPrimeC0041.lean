import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.ReciprocalPrime

noncomputable section

/-- The reciprocal-prime error is positive throughout the finite range in
`C-0041`. -/
def finiteRangePositivity : Prop :=
  ∃ B : ℝ,
    Filter.Tendsto
      (fun n : ℕ ↦
        (∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ)) -
          Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds B) ∧
    ∀ x : ℝ, 1 < x → x ≤ (10 : ℝ) ^ 8 →
      0 <
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / (p : ℝ)) -
          Real.log (Real.log x) - B

/-- The global Axler-shaped lower estimate for the reciprocal-prime error. -/
def globalAxlerDifferentShapeLowerEstimate : Prop :=
  ∃ B : ℝ,
    Filter.Tendsto
      (fun n : ℕ ↦
        (∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ)) -
          Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds B) ∧
    ∀ x : ℝ, 1 < x →
      -1 / (20 * Real.log x ^ 3) - 3 / (16 * Real.log x ^ 4) ≤
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / (p : ℝ)) -
          Real.log (Real.log x) - B

/-- The earlier global reciprocal-prime lower estimate with coefficient one-half. -/
def priorGlobalCoefficientOneHalf : Prop :=
  ∃ B : ℝ,
    Filter.Tendsto
      (fun n : ℕ ↦
        (∑ p ∈ Nat.primesLE n, (1 : ℝ) / (p : ℝ)) -
          Real.log (Real.log (n : ℝ)))
      Filter.atTop (nhds B) ∧
    ∀ x : ℝ, 1 < x →
      -1 / (2 * Real.log x ^ 2) <
        (∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / (p : ℝ)) -
          Real.log (Real.log x) - B

end

end MathlibPlus.Open.NumberTheory.ReciprocalPrime
