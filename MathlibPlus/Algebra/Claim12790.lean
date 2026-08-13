import MathlibPlus.Open.Algebra.Claim12790

namespace MathlibPlus.Algebra

/-- The literal claim 12790 is inconsistent: its displayed polynomial does not
vanish at its displayed roots.  This disproof targets the exact registry node;
it does not replace the node by a repaired polynomial. -/
theorem not_reciprocalGenusOneCounterfeit12790 :
    ¬ MathlibPlus.Open.Algebra.reciprocalGenusOneCounterfeit12790 := by
  intro h
  dsimp [MathlibPlus.Open.Algebra.reciprocalGenusOneCounterfeit12790] at h
  have hα : 1 + 7 * ((-7 + Real.sqrt 13) / 2) +
      9 * ((-7 + Real.sqrt 13) / 2) ^ 2 = 0 := h.2.2.1
  have hs : (Real.sqrt 13) ^ 2 = (13 : ℝ) := by
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hspos : 0 < Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  have hs4 : Real.sqrt 13 < 4 := by nlinarith
  ring_nf at hα
  rw [hs] at hα
  nlinarith [hs4]

end MathlibPlus.Algebra
