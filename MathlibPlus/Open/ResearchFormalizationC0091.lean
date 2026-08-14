import Mathlib

namespace MathlibPlus.Open

/-- Claim 1387: monotonicity and the displayed derivatives of the lower-tail correction. -/
def research_claim_1387 : Prop :=
  let a : ℝ := 15 / 2
  let H : ℝ → ℝ := fun t =>
    (t * Real.log a + 1) * Real.rpow a (-t) +
      t ^ 2 * ∑ n ∈ (Finset.Icc 2 7 : Finset ℕ),
        Real.log (n : ℝ) / Real.rpow (n : ℝ) (1 + t)
  StrictAntiOn H (Set.Ici (4 : ℝ)) ∧
    (∀ t : ℝ, 4 ≤ t →
      deriv (fun x : ℝ => (x * Real.log a + 1) * Real.rpow a (-x)) t =
          -t * (Real.log a) ^ 2 * Real.rpow a (-t) ∧
        -t * (Real.log a) ^ 2 * Real.rpow a (-t) < 0) ∧
    (∀ t : ℝ, 4 ≤ t →
      ∀ n : ℕ, 2 ≤ n → n ≤ 7 →
        deriv (fun x : ℝ =>
            x ^ 2 * Real.log (n : ℝ) / Real.rpow (n : ℝ) (1 + x)) t =
            t * Real.log (n : ℝ) / Real.rpow (n : ℝ) (1 + t) *
              (2 - t * Real.log (n : ℝ)) ∧
          t * Real.log (n : ℝ) / Real.rpow (n : ℝ) (1 + t) *
              (2 - t * Real.log (n : ℝ)) < 0 ∧
          4 * Real.log 2 > 2 ∧
          t * Real.log (n : ℝ) ≥ 4 * Real.log 2)

end MathlibPlus.Open
