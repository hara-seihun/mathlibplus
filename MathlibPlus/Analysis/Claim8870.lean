import Mathlib

namespace MathlibPlus.Analysis.Claim8870

/-- The terminal-packet action is unchanged by the reciprocal-zero reparameterization.
The source's domain is retained explicitly: `z > b = π / 2`. -/
theorem terminalPacketWkbAction_reparam
    (z y : ℝ) (hz : Real.pi / 2 < z)
    (hy : y = 16 * z ^ 2 / Real.pi ^ 2) :
    let b : ℝ := Real.pi / 2
    let action : ℝ → ℝ := fun x =>
      4 * (Real.arcosh (x / b) - Real.sqrt (1 - (b / x) ^ 2))
    let terminal : ℝ → ℝ := fun u =>
      4 * (Real.arcosh (Real.sqrt u / 2) - Real.sqrt (1 - 4 / u))
    action z = terminal y := by
  dsimp
  have hp : 0 < Real.pi := Real.pi_pos
  have hz0 : 0 < z := lt_trans (by positivity) hz
  have hz_ne : z ≠ 0 := ne_of_gt hz0
  have hp_ne : Real.pi ≠ 0 := ne_of_gt hp
  have hy0 : 0 < y := by
    rw [hy]
    positivity
  have hsquare : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt (le_of_lt hy0)
  have hroot : Real.sqrt y = 4 * z / Real.pi := by
    have hnonneg : 0 ≤ 4 * z / Real.pi := by positivity
    have hsnonneg : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    have htarget : (4 * z / Real.pi) ^ 2 = y := by
      rw [hy]
      field_simp [hp_ne]
      ring
    nlinarith
  have harg : (Real.pi / 2 / z) ^ 2 = 4 / y := by
    rw [hy]
    field_simp [hz_ne, hp_ne]
    ring
  have hscale : z / (Real.pi / 2) = Real.sqrt y / 2 := by
    rw [hroot]
    field_simp [hp_ne]
    ring
  rw [hscale, harg]

end MathlibPlus.Analysis.Claim8870
