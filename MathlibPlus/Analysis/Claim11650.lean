import Mathlib

namespace MathlibPlus.Analysis.Claim11650

/-- A finite positive coefficient expansion in odd powers of sech is
strictly positive on the real line. -/
theorem positiveSechShell
    (m : ℕ) (k : ℝ → ℝ) (c : ℕ → ℕ → ℝ)
    (hformula : ∀ d : ℝ,
      k d = ∑ j ∈ Finset.range (m + 1),
        c m j * (1 / Real.cosh d) ^ (2 * j + 1))
    (hc : ∀ j, j ≤ m → 0 < c m j) :
    ∀ d : ℝ, 0 < k d := by
  intro d
  rw [hformula d]
  apply Finset.sum_pos
  · intro j hj
    have hjm : j ≤ m := by
      simpa [Finset.mem_range] using hj
    exact mul_pos (hc j hjm) (pow_pos (by positivity) _)
  · exact ⟨0, by simp⟩

end MathlibPlus.Analysis.Claim11650
