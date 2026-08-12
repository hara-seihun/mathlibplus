import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 25740: at fixed deck order, every linear deck coordinate is the
rational falling-quadratic combination of the ordered distinct-card rows. -/
theorem linearDeckRowInFallingQuadraticSpan_claim25740
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℚ) (n : ℕ) (h_total : ∑ H, d H = (n : ℚ))
    (h_n : 1 < n) (F : ι) :
    d F = ((n : ℚ) - 1)⁻¹ *
      ∑ H, (if F = H then d F * (d F - 1) else d F * d H) := by
  have hsum :
      ∑ H, (if F = H then d F * (d F - 1) else d F * d H) =
        ((n : ℚ) - 1) * d F := by
    calc
      ∑ H, (if F = H then d F * (d F - 1) else d F * d H) =
          ∑ H, (d F * d H - if F = H then d F else 0) := by
            apply Finset.sum_congr rfl
            intro H hH
            by_cases h : F = H <;> simp [h]
            · ring
      _ = d F * ∑ H, d H - d F := by
            rw [Finset.mul_sum]
            simp
      _ = ((n : ℚ) - 1) * d F := by
            rw [h_total]
            ring
  rw [hsum]
  have hnq : (n : ℚ) - 1 ≠ 0 := by
    have hnq' : (1 : ℚ) < (n : ℚ) := by exact_mod_cast h_n
    linarith
  field_simp

end MathlibPlus.Combinatorics
