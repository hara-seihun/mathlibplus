import Mathlib

/-!
# An individual Arthur weight outside the reflected cone

Registry statement for admitted claim 284.  The decimal diagnostics in the
source have no stated error intervals, so the exact transcendental quantities
and their strict signs are recorded instead.
-/

namespace MathlibPlus.Open.NumberTheory.ArthurWeight

/-- The weight `(m₇, m₅₃) = (2, -1)` in the coefficient at `7² * 53` has
positive direct and reflected energies but negative signed cone energy, while
the complete coefficient remains positive. -/
noncomputable def individualWeightConeCounterexample : Prop :=
  let tau7 : ℤ := -16744
  let tau53 : ℤ := -1596055698
  let phi7 : ℝ := Real.arccos (((tau7 : ℝ) ^ 2) / (2 * (7 : ℝ) ^ 11) - 1)
  let phi53 : ℝ := Real.arccos (((tau53 : ℝ) ^ 2) / (2 * (53 : ℝ) ^ 11) - 1)
  let U : ℝ := 11 * Real.log (((7 : ℝ) ^ 2) / 53)
  let Phi : ℝ := 2 * phi7 - phi53
  let directEnergy : ℝ := Real.exp U + Real.exp (-U) - 2 * Real.cos Phi
  let reflectedEnergy : ℝ := Real.exp U + Real.exp (-U) + 2 * Real.cos Phi
  let q7 : ℝ := (7 : ℝ) ^ 11
  let q53 : ℝ := (53 : ℝ) ^ 11
  let split7Degree2 : ℝ := q7 ^ 2 + q7 + 2 + q7⁻¹ + q7⁻¹ ^ 2
  let split53Degree1 : ℝ := q53 + 1 + q53⁻¹
  let compact7Degree2 : ℝ := 2 + 2 * Real.cos phi7 + 2 * Real.cos (2 * phi7)
  let compact53Degree1 : ℝ := 1 + 2 * Real.cos phi53
  let completeCoefficient : ℝ :=
    split7Degree2 * split53Degree1 +
      3 * (compact7Degree2 * compact53Degree1) - 8
  0 < directEnergy ∧
    0 < reflectedEnergy ∧
    2 * reflectedEnergy - directEnergy < 0 ∧
    0 < completeCoefficient

end MathlibPlus.Open.NumberTheory.ArthurWeight
