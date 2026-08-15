import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.K0163

def claim9732 : Prop :=
  let n₀ : ℕ := 160626866400
  let y : ℝ := Real.log (n₀ : ℝ)
  let G : ℕ → ℝ := fun n =>
    (∑ d ∈ n.divisors, (d : ℝ)) /
      ((n : ℝ) * Real.log (Real.log (n : ℝ)))
  let F : ℕ → ℕ → ℝ := fun p k =>
    let L : ℝ := Real.log (p : ℝ)
    L⁻¹ * Real.log
      (1 + (∑ i ∈ Finset.Icc 1 k, (p : ℝ) ^ i)⁻¹)
  let eta : ℕ → ℝ → ℝ := fun p z =>
    (Real.log (p : ℝ))⁻¹ *
      Real.log (Real.log (z + Real.log (p : ℝ)) / Real.log z)
  (∀ q : ℕ, Nat.Prime q → q < 31 →
      (¬ q ∣ n₀ ↔ q = 29)) ∧
    (∀ p : ℕ, Nat.Prime p → 31 ≤ p →
      F p 1 < 1 / ((p : ℝ) * Real.log (p : ℝ)) ∧
        1 / ((p : ℝ) * Real.log (p : ℝ)) <
          1 / ((y + Real.log (p : ℝ)) *
            Real.log (y + Real.log (p : ℝ))) ∧
        1 / ((y + Real.log (p : ℝ)) *
            Real.log (y + Real.log (p : ℝ))) < eta p y) ∧
    (∀ p : ℕ, Nat.Prime p → G (n₀ * p) < G n₀)

end MathlibPlus.Open.Research.K0163
