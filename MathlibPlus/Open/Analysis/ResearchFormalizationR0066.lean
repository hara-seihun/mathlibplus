import Mathlib

open MeasureTheory

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0066

noncomputable section

/-- The full divided-jet carrier from the admitted integral formula. -/
private noncomputable def fullDividedJet (r : ℕ) (lam : ℝ) : ℝ :=
  (2 / (Nat.factorial r : ℝ)) *
    ∫ u in Set.Ioi (0 : ℝ),
      u ^ r * Real.exp (u / 2 - lam * Real.exp (2 * u))

/-- Claim 17639: the triangular differential recurrence for the divided jets. -/
def claim17639_triangularJetRecurrence : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ (lam : ℝ), 0 < lam →
    lam * deriv (fullDividedJet r) lam +
        (1 / 4 : ℝ) * fullDividedJet r lam =
      -(1 / 2 : ℝ) * fullDividedJet (r - 1) lam

/-- Claim 17640: the inhomogeneous boundary equation for the zeroth jet. -/
def claim17640_inhomogeneousBoundaryEquation : Prop :=
  ∀ (lam : ℝ), 0 < lam →
    lam * deriv (fullDividedJet 0) lam +
        (1 / 4 : ℝ) * fullDividedJet 0 lam =
      -Real.exp (-lam)

end

end MathlibPlus.Open.Analysis.ResearchFormalizationR0066
