import Mathlib

namespace MathlibPlus.Algebra.PositiveGradedNotPure

/-- Claim 12716: positive coefficients of the quadratic `1+7u+9u²` do not
force its reciprocal roots to have a common modulus. -/
theorem positiveGradedDimensionsDoNotForcePurity :
    let C : ℝ → ℝ := fun u => 1 + 7 * u + 9 * u ^ 2
    let Q : ℝ → ℝ := fun u => u ^ 2 + 7 * u + 9
    let rPlus : ℝ := (-7 + Real.sqrt 13) / 2
    let rMinus : ℝ := (-7 - Real.sqrt 13) / 2
    (0 < (1 : ℝ) ∧ 0 < (7 : ℝ) ∧ 0 < (9 : ℝ)) ∧
      (∀ u : ℝ, u ≠ 0 → u ^ 2 * C (1 / u) = Q u) ∧
      Q rPlus = 0 ∧ Q rMinus = 0 ∧
      rPlus * rMinus = 9 ∧
      |rPlus| ≠ |rMinus| ∧
      ¬(|rPlus| = 3 ∧ |rMinus| = 3) := by
  dsimp
  have hs : (Real.sqrt (13 : ℝ)) ^ 2 = 13 := by
    simpa using (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 13))
  have hpos : 0 < Real.sqrt (13 : ℝ) := by positivity
  have hlt : Real.sqrt (13 : ℝ) < 7 := by nlinarith
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    field_simp [hu]
  · nlinarith [hs]
  · nlinarith [hs]
  · nlinarith [hs]
  · have hpneg : (-7 + Real.sqrt (13 : ℝ)) / 2 < 0 := by linarith
    have hmneg : (-7 - Real.sqrt (13 : ℝ)) / 2 < 0 := by linarith
    rw [abs_of_neg hpneg, abs_of_neg hmneg]
    intro h
    nlinarith
  · have hpneg : (-7 + Real.sqrt (13 : ℝ)) / 2 < 0 := by linarith
    have hmneg : (-7 - Real.sqrt (13 : ℝ)) / 2 < 0 := by linarith
    rw [abs_of_neg hpneg, abs_of_neg hmneg]
    rintro ⟨hp3, hm3⟩
    nlinarith

end MathlibPlus.Algebra.PositiveGradedNotPure
