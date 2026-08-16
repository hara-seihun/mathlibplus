import Mathlib

noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

/-- Direct Arthur energy for the paired parameters `(U, Φ)`. -/
def directArthurEnergy12140 (U Φ : ℝ) : ℝ :=
  Real.exp U + Real.exp (-U) - 2 * Real.cos Φ

/-- Reflected Arthur energy for the paired parameters `(U, Φ)`. -/
def reflectedArthurEnergy12140 (U Φ : ℝ) : ℝ :=
  Real.exp U + Real.exp (-U) + 2 * Real.cos Φ

/-- One-weight reflected cone formula. -/
def oneWeightReflectedConeFormula12141 (U Φ : ℝ) : Prop :=
  2 * reflectedArthurEnergy12140 U Φ - directArthurEnergy12140 U Φ =
    Real.exp U + Real.exp (-U) + 6 * Real.cos Φ

end MathlibPlus.Open.ProjectsResearch
