import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0148Claim18292

/-- The rational wall factor from the half-shift gamma spinor. -/
noncomputable def gammaWallFactor (z : ℝ) : ℝ :=
  ((2 * z + 5) * (2 * z + 3)) / (4 * Real.pi * (2 * z - 1))

/-- The orientation-line determinant is the negative of the wall factor. -/
noncomputable def gammaSpinorDeterminant (z : ℝ) : ℝ :=
  -gammaWallFactor z

/-- The pole wall is the zero set of the displayed denominator. -/
def gammaWallPole (z : ℝ) : Prop :=
  2 * z - 1 = 0

/-- The determinant carrier is defined away from its pole wall. -/
def gammaWallDefined (z : ℝ) : Prop :=
  ¬gammaWallPole z

/-- Claim 18292: the half-shift gamma determinant has exactly the two zero
walls and the pole wall, with the four displayed chamber signs. -/
def exactGammaWallSignChart18292 : Prop :=
  (∀ z : ℝ, gammaWallPole z ↔ z = (1 / 2 : ℝ)) ∧
    (∀ z : ℝ, gammaWallDefined z →
      (gammaSpinorDeterminant z = 0 ↔
        z = (-5 / 2 : ℝ) ∨ z = (-3 / 2 : ℝ))) ∧
    gammaWallDefined (-5 / 2 : ℝ) ∧
    gammaWallDefined (-3 / 2 : ℝ) ∧
    gammaWallPole (1 / 2 : ℝ) ∧
    (∀ z : ℝ, z < (-5 / 2 : ℝ) →
      0 < gammaSpinorDeterminant z) ∧
    (∀ z : ℝ, (-5 / 2 : ℝ) < z → z < (-3 / 2 : ℝ) →
      gammaSpinorDeterminant z < 0) ∧
    (∀ z : ℝ, (-3 / 2 : ℝ) < z → z < (1 / 2 : ℝ) →
      0 < gammaSpinorDeterminant z) ∧
    (∀ z : ℝ, (1 / 2 : ℝ) < z →
      gammaSpinorDeterminant z < 0)

end MathlibPlus.Open.ResearchFormalization.R0148Claim18292
