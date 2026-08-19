import Mathlib

namespace MathlibPlus.AlgebraicGeometry.Q0100Q0103

/-- Claim 14594: the displayed Chern-square plus second-Chern sum is exactly
12, hence divisible by 12. -/
def noetherFormulaDivisibility_claim14594 : Prop :=
  (12 : ℤ) ∣ ((2 : ℤ) + 10) ∧
    ((2 : ℤ) + 10 = 12)

/-- Claim 14612: both displayed candidate Chern numbers are positive. -/
def positiveCandidateChernNumbers_claim14612 : Prop :=
  (0 : ℤ) < 5 ∧ (0 : ℤ) < 7

end MathlibPlus.AlgebraicGeometry.Q0100Q0103
