import Mathlib

namespace MathlibPlus.Analysis

/-- The exact current-episode recurrence and its closed form from claim 50301.
The posterior-variance and independent-coordinate carriers are not introduced
here because the packet does not define them separately. -/
theorem parityEpisodeRecurrence_solution_claim50301
    (Φ : ℕ → ℚ)
    (h0 : Φ 0 = 0)
    (hrec : ∀ r : ℕ, Φ (r + 1) = 1 + (1 / 2 : ℚ) * Φ r) :
    ∀ r : ℕ, Φ r = 2 * (1 - (1 / 2 : ℚ) ^ r) := by
  intro r
  induction r with
  | zero =>
      norm_num [h0]
  | succ r ihr =>
      rw [hrec, ihr]
      ring

/-- A uniform positive transfer estimate forces the corresponding pointwise
weight lower bound at every positive integer, as in claim 18764. -/
theorem weightedTransfer_lowerBound_claim18764
    (w : ℕ → ℝ) (C σ₀ σ₁ : ℝ)
    (hC : 0 < C)
    (h : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (-σ₁) ≤ C * w n * (n : ℝ) ^ (-σ₀)) :
    ∀ n : ℕ, 0 < n → C⁻¹ * (n : ℝ) ^ (σ₀ - σ₁) ≤ w n := by
  intro n hn
  have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpow : 0 < (n : ℝ) ^ (-σ₀) := Real.rpow_pos_of_pos hx _
  have hden : 0 < C * (n : ℝ) ^ (-σ₀) := mul_pos hC hpow
  have hdiv : (n : ℝ) ^ (-σ₁) / (C * (n : ℝ) ^ (-σ₀)) ≤ w n := by
    apply (div_le_iff₀ hden).2
    calc
      (n : ℝ) ^ (-σ₁) ≤ C * w n * (n : ℝ) ^ (-σ₀) := h n hn
      _ = w n * (C * (n : ℝ) ^ (-σ₀)) := by ring
  calc
    C⁻¹ * (n : ℝ) ^ (σ₀ - σ₁) =
        (n : ℝ) ^ (-σ₁) / (C * (n : ℝ) ^ (-σ₀)) := by
      rw [Real.rpow_sub hx, Real.rpow_neg (le_of_lt hx)]
      field_simp
      rw [← Real.rpow_add hx]
      norm_num
    _ ≤ w n := hdiv

end MathlibPlus.Analysis
