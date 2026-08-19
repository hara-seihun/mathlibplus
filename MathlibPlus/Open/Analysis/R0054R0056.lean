import Mathlib
import MathlibPlus.Analysis.ThetaMellin

namespace MathlibPlus.Open.Analysis.R0054R0056

noncomputable section

open MathlibPlus.Analysis.ThetaMellin

def claim17521_thetaShellTranslation : Prop :=
  ∀ n : ℕ, 0 < n → ∀ u : ℝ,
    thetaShell n u =
      (n : ℝ) ^ (-(1 : ℝ) / 2) *
        thetaShell 1 (u + Real.log (n : ℝ))

def shiftedDivisorCoordinate (R d : ℕ) (α : ℝ) : ℝ :=
  Real.log (d : ℝ) - α * Real.log (R : ℝ)

def claim17534_halfCenteringExponent : Prop :=
  ∀ R : ℕ, 1 < R → ∀ α : ℝ,
    ((∀ d : ℕ, 0 < d → d ∣ R →
      shiftedDivisorCoordinate R (R / d) α =
        -shiftedDivisorCoordinate R d α) ↔
      α = (1 : ℝ) / 2)

def transferMultiplier (z : ℝ) : ℝ :=
  ((2 * z + 5) * (2 * z + 3)) /
    (4 * Real.pi * (2 * z - 1))

def claim17539_transferMultiplierPositive : Prop :=
  ∀ z : ℝ, -(1 : ℝ) / 2 < z → z < (1 : ℝ) / 2 →
    -transferMultiplier z > 0

end

end MathlibPlus.Open.Analysis.R0054R0056
