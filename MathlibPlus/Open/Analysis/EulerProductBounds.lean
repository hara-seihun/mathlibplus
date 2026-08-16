import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 11855: the local-factor bounds for primes beyond 100. -/
def prime_local_factor_bounds_beyond_100 : Prop :=
  ∀ p : ℕ, Nat.Prime p → 100 < p →
    let u_p : ℝ := 2 / (p : ℝ) ^ 2 - 1 / (p : ℝ) ^ 3
    let D : ℝ := 1 - 2 / (101 : ℝ) ^ 2
    (0 < u_p ∧ u_p < 2 / (p : ℝ) ^ 2) ∧
      (D < 1 - u_p ∧ 0 < D)

/-- Claim 11858: the logarithmic and ordinary lower bounds for the tail product. -/
def infinite_tail_product_lower_bound : Prop :=
  let D : ℝ := 1 - 2 / (101 : ℝ) ^ 2
  let tail : ℝ :=
    ∏' q : {q : ℕ // Nat.Prime q ∧ 100 < q},
      (1 - (2 / (q.1 : ℝ) ^ 2 - 1 / (q.1 : ℝ) ^ 3))
  (Real.log tail > -(2 : ℝ) / (100 * D)) ∧
    tail > 1 - 2 / (100 * D)

/-- Claim 11859: the displayed finite-times-tail product chain. -/
def displayed_product_gt_0421 : Prop :=
  let D : ℝ := 1 - 2 / (101 : ℝ) ^ 2
  let W : ℝ :=
    ∏' q : {q : ℕ // Nat.Prime q},
      (1 - (2 / (q.1 : ℝ) ^ 2 - 1 / (q.1 : ℝ) ^ 3))
  let P100 : ℝ :=
    Finset.prod (Finset.filter Nat.Prime (Finset.range 101))
      (fun q => 1 - (2 / (q : ℝ) ^ 2 - 1 / (q : ℝ) ^ 3))
  let tail : ℝ :=
    ∏' q : {q : ℕ // Nat.Prime q ∧ 100 < q},
      (1 - (2 / (q.1 : ℝ) ^ 2 - 1 / (q.1 : ℝ) ^ 3))
  (W = P100 * tail) ∧
    (P100 * tail > P100 * (1 - 2 / (100 * D))) ∧
    (P100 * (1 - 2 / (100 * D)) > (421 : ℝ) / 1000)

end

end MathlibPlus.Open.Analysis
