import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ReciprocalDivisorBatch

/-- Claim 17599: ratio limits peel a dominant reciprocal-divisor atom. -/
def claim17599 : Prop :=
  ∀ (d : ℕ → ℂ) (K : Finset ℕ) (c : ℕ → ℂ),
    (∀ j, d j ≠ 0) →
    (∀ R : ℝ, 0 < R →
      Set.Finite {j : ℕ | R ≤ ‖(d j)⁻¹‖}) →
    (∀ n : ℕ, 0 < n →
      c n = ∑' j : ℕ, if j ∈ K then 0 else (d j)⁻¹ ^ n) →
    (∃ u : ℂ, ‖u‖ = 1 ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c n ≠ 0 ∧ c n / (‖c n‖ : ℂ) = u) →
    (∃ r : ℂ, r ≠ 0 ∧
      Filter.Tendsto (fun n : ℕ => c (n + 1) / c n) Filter.atTop (nhds r)) →
    ∃ (u r : ℂ),
      ‖u‖ = 1 ∧
      (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c n ≠ 0 ∧ c n / (‖c n‖ : ℂ) = u) ∧
      r ≠ 0 ∧
        Filter.Tendsto (fun n : ℕ => c (n + 1) / c n) Filter.atTop (nhds r) ∧
      ∃ j : ℕ, j ∉ K ∧ (d j)⁻¹ = r ∧
        ∃ t : ℝ, 0 < t ∧ r = (t : ℂ) * u

end MathlibPlus.Open.Analysis.ReciprocalDivisorBatch
