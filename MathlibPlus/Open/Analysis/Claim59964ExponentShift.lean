import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- Claim 59964: the uniform exponent-shift obstruction. -/
def claim59964_uniformExponentShiftObstruction : Prop :=
  ∀ C A : ℝ,
    0 < C →
      ∃ N m : ℕ,
        0 < N ∧
          0 < m ∧
            N = m ∧
              (m : ℝ) ^ 2 ≥
                (3 / (2 * Real.pi)) * (N : ℝ) + A * Real.sqrt (N : ℝ) ∧
                Real.exp
                    ((3 / 2 : ℝ) * (N : ℝ) -
                      Real.pi * ((m : ℝ) - 1) ^ 2) >
                  C * Real.rpow (N : ℝ) A *
                    Real.exp
                      ((3 / 2 : ℝ) * (N : ℝ) - Real.pi * (m : ℝ) ^ 2)

end MathlibPlus.Open.Analysis
