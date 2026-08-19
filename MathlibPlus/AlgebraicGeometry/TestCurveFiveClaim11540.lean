import Mathlib

namespace MathlibPlus.AlgebraicGeometry.TestCurveFive

/-- Claim 11540: the integral test curve has discriminant `-496`, whose
reduction at five is nonsingular; its associated base-changed five-adic curve
has good reduction. -/
def testCurve_goodReduction_claim11540 : Prop :=
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let E : WeierstrassCurve ℤ := ⟨0, 0, 0, 1, 1⟩
  let E5 : WeierstrassCurve ℚ_[5] := E.baseChange ℚ_[5]
  E.Δ = (-496 : ℤ) ∧
    (E.Δ : ZMod 5) ≠ 0 ∧
    E5.HasGoodReduction (ℤ_[5])

end MathlibPlus.AlgebraicGeometry.TestCurveFive
