import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Analysis.WeightedVariance

/--
Claim 29352.  This is the finite weighted form of the constant-carrier
minimization.  The source weights are `|a_{j,n}|²`; the theorem states the
same algebra for arbitrary nonnegative finite weights.  The explicit
positivity of `S₀` is the nonzero denominator condition implicit in the
source's optimizer `S₁ / S₀`.
-/
theorem constantCarrierWeightedVariance_minimum_claim29352
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (lam w : ι → ℝ)
    (hS0 : 0 < ∑ n ∈ s, w n) :
    let S0 := ∑ n ∈ s, w n
    let S1 := ∑ n ∈ s, lam n * w n
    let S2 := ∑ n ∈ s, lam n ^ 2 * w n
    let V := S2 - S1 ^ 2 / S0
    ∀ ω : ℝ,
      V ≤ ∑ n ∈ s, (lam n - ω) ^ 2 * w n ∧
        (∑ n ∈ s, (lam n - S1 / S0) ^ 2 * w n) = V := by
  dsimp
  let S0 : ℝ := ∑ n ∈ s, w n
  let S1 : ℝ := ∑ n ∈ s, lam n * w n
  let S2 : ℝ := ∑ n ∈ s, lam n ^ 2 * w n
  let V : ℝ := S2 - S1 ^ 2 / S0
  have hS0' : 0 < S0 := hS0
  have h_expand (ω : ℝ) :
      (∑ n ∈ s, (lam n - ω) ^ 2 * w n) =
        S2 - 2 * ω * S1 + ω ^ 2 * S0 := by
    calc
      (∑ n ∈ s, (lam n - ω) ^ 2 * w n) =
          ∑ n ∈ s, (lam n ^ 2 * w n - (2 * ω) * (lam n * w n) +
            ω ^ 2 * w n) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
      _ = S2 - 2 * ω * S1 + ω ^ 2 * S0 := by
        simp only [S0, S1, S2]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [Finset.mul_sum, Finset.mul_sum]
  have h_complete (ω : ℝ) :
      (∑ n ∈ s, (lam n - ω) ^ 2 * w n) =
        V + S0 * (ω - S1 / S0) ^ 2 := by
    rw [h_expand]
    dsimp [V]
    field_simp [ne_of_gt hS0']
    ring
  intro ω
  constructor
  · rw [h_complete]
    have hnonneg : 0 ≤ S0 * (ω - S1 / S0) ^ 2 :=
      mul_nonneg (le_of_lt hS0') (sq_nonneg _)
    linarith
  · simpa [S0, S1, S2, V] using h_complete (S1 / S0)

end MathlibPlus.Analysis.WeightedVariance
