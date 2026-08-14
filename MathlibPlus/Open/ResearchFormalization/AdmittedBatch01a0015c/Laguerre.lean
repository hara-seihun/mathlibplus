import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators
open MeasureTheory

/-- Claim 14367: the exact Laguerre transform pole. -/
def claim14367 : Prop :=
  ∀ (δ : ℝ), 0 < δ →
    ∀ n : ℕ, 2 ≤ n →
      let rδ : ℝ := -(1 - δ) / δ
      let laguerreTwo : ℕ → ℝ → ℝ := fun m t =>
        ∑ k ∈ Finset.range (m + 1),
          (-1 : ℝ) ^ k * (Nat.choose (m + 2) (m - k) : ℝ) * t ^ k /
            (Nat.factorial k : ℝ)
      (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-δ * t) * laguerreTwo (n - 2) t) =
        (n : ℝ) - δ + δ * rδ ^ n

end MathlibPlus.Open.ResearchFormalization
