import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.AnalyticNumberTheory.BatchO0312.Floor

/-- A finite positive index set carrying the coefficient family. -/
def positiveDivisorSupport (D : Finset ℕ) : Prop :=
  ∀ d ∈ D, 0 < d

/-- The coefficient family vanishes outside its finite displayed support. -/
def finiteCoefficientSupport (D : Finset ℕ) (c : ℕ → ℂ) : Prop :=
  ∀ n, n ∉ D → c n = 0

/-- The literal divisor-convolution coefficient `b_c(n)`. -/
noncomputable def divisorCoefficient
    (D : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ D.filter (fun d => d ∣ n), c d

/-- The partial sum over the positive integers `n ≤ x`. -/
noncomputable def coefficientPartialSum
    (D : Finset ℕ) (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nat.floor x), divisorCoefficient D c n

/-- Claim 15290: pole cancellation gives the exact floor and fractional-part
forms of the positive-index coefficient partial sums, and boundedness. -/
def claim15290_exactFloorPartialSums : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ → ℂ),
    positiveDivisorSupport D →
    finiteCoefficientSupport D c →
    (∑ d ∈ D, c d / (d : ℂ)) = 0 →
    (∀ x : ℝ, 1 ≤ x →
      let B := coefficientPartialSum D c x
      B = ∑ d ∈ D,
        c d * (Nat.floor (x / (d : ℝ)) : ℂ) ∧
      B = -∑ d ∈ D,
        c d * ((Int.fract (x / (d : ℝ)) : ℝ) : ℂ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 1 ≤ x → ‖coefficientPartialSum D c x‖ ≤ C)

end MathlibPlus.Open.AnalyticNumberTheory.BatchO0312.Floor
