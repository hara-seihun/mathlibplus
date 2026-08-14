import Mathlib.Analysis.Real.Pi.Bounds

namespace MathlibPlus.Open.Analysis.Batch545

/-- Claim 54552: the exact rational parameter pair satisfies the target-ray
geometry inequalities. -/
def exactTargetRayGeometry_claim54552 : Prop :=
  let L : ℝ := 1529 / 10000
  let tStar : ℝ := 1479 / 10000
  let y : ℝ := 1 / 10
  let X : ℝ := 6000000185827
  let zStar : ℂ := (2 * X + 1) * Real.pi + Complex.I * y
  tStar + y ^ 2 / 2 = L ∧
    y ^ 2 < 1 - 2 * tStar ∧
      Complex.re zStar > X + Real.sqrt (1 - y ^ 2)

end MathlibPlus.Open.Analysis.Batch545
