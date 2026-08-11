import Mathlib

namespace MathlibPlus.Algebra.Claim27412

/-- Claim 27412: exact improved-triangle domination inequality. -/
theorem exactImprovedTriangleDomination (A B a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    let F := B - a * A
    let K := A - a * B
    B - A = (F - K) / (1 + a) ∧
      (1 - a) / (1 + a) * (B + A) = (F + K) / (1 + a) ∧
      max (|B - A|) ((1 - a) / (1 + a) * |B + A|) ≤
        (|F| + |K|) / (1 + a) := by
  dsimp
  have hden : 0 < 1 + a := by linarith
  have hden0 : (1 + a : ℝ) ≠ 0 := ne_of_gt hden
  have h1 : B - A = ((B - a * A) - (A - a * B)) / (1 + a) := by
    field_simp
    ring
  have h2 : (1 - a) / (1 + a) * (B + A) =
      ((B - a * A) + (A - a * B)) / (1 + a) := by
    field_simp
    ring
  refine ⟨h1, h2, ?_⟩
  rw [h1]
  apply max_le
  · calc
      |((B - a * A) - (A - a * B)) / (1 + a)| =
          |(B - a * A) - (A - a * B)| / |1 + a| := by rw [abs_div]
      _ = |(B - a * A) - (A - a * B)| / (1 + a) := by rw [abs_of_pos hden]
      _ ≤ (|B - a * A| + |A - a * B|) / (1 + a) := by
        gcongr
        simpa [abs_sub_comm] using abs_sub_le (B - a * A) 0 (A - a * B)
  · have hcoef : 0 ≤ (1 - a) / (1 + a) := by positivity
    calc
      (1 - a) / (1 + a) * |B + A| =
          |(1 - a) / (1 + a)| * |B + A| := by rw [abs_of_nonneg hcoef]
      _ = |(1 - a) / (1 + a) * (B + A)| := by rw [abs_mul]
      _ = |((B - a * A) + (A - a * B)) / (1 + a)| := by rw [h2]
      _ = |(B - a * A) + (A - a * B)| / |1 + a| := by rw [abs_div]
      _ = |(B - a * A) + (A - a * B)| / (1 + a) := by rw [abs_of_pos hden]
      _ ≤ (|B - a * A| + |A - a * B|) / (1 + a) := by
        gcongr
        exact abs_add_le (B - a * A) (A - a * B)

end MathlibPlus.Algebra.Claim27412
