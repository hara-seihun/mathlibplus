import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra

/-- Claim 4761: the factorial normalization has the equivalent half-rising-factorial form.
The rising factorial `(1/2)_n` is written as the displayed finite product. -/
theorem normalizedCoefficientFormula (n : ℕ) (m : ℝ) :
    (n.factorial : ℝ) * m / (2 * n).factorial =
      m / ((4 : ℝ) ^ n * ∏ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2) := by
  have hfactorial : ((2 * n).factorial : ℝ) =
      (4 : ℝ) ^ n * (n.factorial : ℝ) *
        ∏ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        have htwo : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
        rw [htwo]
        simp only [Nat.factorial_succ]
        push_cast
        rw [ih, Finset.prod_range_succ]
        have hterm (k : ℕ) :
            ((2 * k + 1 : ℕ) : ℝ) / 2 = (1 / 2 : ℝ) + k := by
          push_cast
          ring
        simp_rw [hterm]
        ring
  rw [hfactorial]
  have hprod : (0 : ℝ) < ∏ k ∈ Finset.range n, ((2 * k + 1 : ℕ) : ℝ) / 2 := by
    positivity
  field_simp [hprod.ne', Nat.factorial_ne_zero]

end MathlibPlus.Algebra
