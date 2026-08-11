import Mathlib

namespace MathlibPlus.Analysis.MomentRatios

/-- The consecutive scale-free moment ratio is unchanged when all moments are
multiplied by one positive mass and the underlying support is dilated positively. -/
theorem consecutiveRatio_mass_dilation_invariant
    (m : ℕ → ℝ) (hm : ∀ j, 0 < m j) (mass scale : ℝ)
    (hmass : 0 < mass) (hscale : 0 < scale) (k : ℕ) :
    ((mass * scale ^ k * m k) * (mass * scale ^ (k + 2) * m (k + 2))) /
        (mass * scale ^ (k + 1) * m (k + 1)) ^ 2 =
      (m k * m (k + 2)) / (m (k + 1)) ^ 2 := by
  have hmass0 : mass ≠ 0 := ne_of_gt hmass
  have hscale0 : scale ≠ 0 := ne_of_gt hscale
  have hm0 (j : ℕ) : m j ≠ 0 := ne_of_gt (hm j)
  have hpow : scale ^ k * scale ^ (k + 2) = (scale ^ (k + 1)) ^ 2 := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  field_simp
  calc
    scale ^ k * m k * scale ^ (k + 2) * m (k + 2) / m (k + 1) ^ 2 =
        (scale ^ k * scale ^ (k + 2)) * (m k * m (k + 2)) / m (k + 1) ^ 2 := by ring
    _ = (scale ^ (k + 1)) ^ 2 * (m k * m (k + 2)) / m (k + 1) ^ 2 := by rw [hpow]
    _ = m k * m (k + 2) * (scale ^ (k + 1)) ^ 2 / m (k + 1) ^ 2 := by ring

end MathlibPlus.Analysis.MomentRatios
