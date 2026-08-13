import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Analysis

/-- The positive tail in the coefficient formula of admitted claim 3050.
The summability hypothesis is the local formal interface for evaluating the
entire coefficient series at the positive point `α`. -/
theorem claim3050_positiveGeometricTail
    (a c : ℕ → ℝ) (α : ℝ)
    (hα : 0 < α)
    (ha : ∀ n, 0 < a n)
    (hsum : ∀ n, Summable (fun j : ℕ => a (n + 1 + j) * α ^ j))
    (hc : ∀ n, c n = ∑' j : ℕ, a (n + 1 + j) * α ^ j) :
    ∀ n, 0 < c n := by
  intro n
  rw [hc n]
  have hnonneg : ∀ j : ℕ, 0 ≤ a (n + 1 + j) * α ^ j := by
    intro j
    exact mul_nonneg (le_of_lt (ha _)) (pow_nonneg (le_of_lt hα) _)
  have hzero : 0 < a (n + 1 + 0) * α ^ 0 := by
    simpa using ha (n + 1)
  exact (hsum n).tsum_pos hnonneg 0 hzero

end MathlibPlus.Analysis
