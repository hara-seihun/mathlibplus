import Mathlib

namespace MathlibPlus.Analysis.Claim8958

/-- The explicit equilibrium density in the packet obeys its exact dilation law. -/
theorem exactDilationLaw (α z : ℝ) (hα : 0 < α) (hz : 0 < z) :
    let ρ : ℝ → ℝ → ℝ := fun a x =>
      if x < Real.pi / (2 * a) then
        (1 / (a * x ^ 2)) *
          (1 - Real.sqrt (1 - (x / (Real.pi / (2 * a))) ^ 2))
      else
        1 / (a * x ^ 2)
    ρ α z = α * ρ 1 (α * z) := by
  dsimp
  have hπ : 0 < Real.pi := Real.pi_pos
  have hαne : α ≠ 0 := ne_of_gt hα
  have hzne : z ≠ 0 := ne_of_gt hz
  by_cases h : z < Real.pi / (2 * α)
  · have h' : α * z < Real.pi / 2 := by
      have hm : z * (2 * α) < Real.pi :=
        (lt_div_iff₀ (by positivity)).1 h
      nlinarith
    have h'' : α * z < Real.pi / (2 * 1) := by
      simpa using h'
    rw [if_pos h, if_pos h'']
    simp only [mul_one, one_mul]
    have hratio : z / (Real.pi / (2 * α)) =
        (α * z) / (Real.pi / 2) := by
      field_simp [hαne, hπ.ne']
    have hpref : 1 / (α * z ^ 2) =
        α * (1 / (1 * (α * z) ^ 2)) := by
      field_simp [hαne, hzne]
    rw [hratio, hpref]
    ring
  · have h' : ¬ α * z < Real.pi / 2 := by
      intro h'
      apply h
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith [h']
    have h'' : ¬ α * z < Real.pi / (2 * 1) := by
      simpa using h'
    rw [if_neg h, if_neg h'']
    simp only [one_mul]
    field_simp [hαne, hzne]

end MathlibPlus.Analysis.Claim8958
