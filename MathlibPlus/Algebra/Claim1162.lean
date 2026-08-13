import Mathlib

namespace MathlibPlus.Algebra.Claim1162

/--
The three displayed linear denominators occur among the pair-sum factors at
explicit pairs `(0,d-1)`, `(0,d)`, and `(1,d)`, respectively.  The hypotheses
`d ≥ 2` are exactly those needed for these pairs to lie in the indexed product.
-/
theorem pair_sum_factor_witnesses_claim1162 (d : ℕ) (hd : 2 ≤ d) (b : ℝ) :
    let X : ℝ := 2 * b + (d : ℝ) + 1
    (∃ p ∈ Finset.range (d + 1), ∃ q ∈ Finset.Ioc p d,
      p + q = d - 1 ∧ 2 * b + (p : ℝ) + (q : ℝ) + 1 = X - 1) ∧
    (∃ p ∈ Finset.range (d + 1), ∃ q ∈ Finset.Ioc p d,
      p + q = d ∧ 2 * b + (p : ℝ) + (q : ℝ) + 1 = X) ∧
    (∃ p ∈ Finset.range (d + 1), ∃ q ∈ Finset.Ioc p d,
      p + q = d + 1 ∧ 2 * b + (p : ℝ) + (q : ℝ) + 1 = X + 1) := by
  dsimp
  constructor
  · refine ⟨0, by simp, d - 1, ?_, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
    · rw [Nat.cast_sub (by omega)]
      ring
  constructor
  · refine ⟨0, by simp, d, ?_, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
    · ring
  · refine ⟨1, by simp; omega, d, ?_, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · omega
    · norm_num
      ring

/-- The remaining scalar denominator in the area-two formulas divides `d!`. -/
theorem scalar_denominator_dvd_factorial_claim1162 (d : ℕ) (hd : 2 ≤ d) :
    2 ∣ d.factorial := by
  exact Nat.dvd_factorial (by omega) hd

end MathlibPlus.Algebra.Claim1162
