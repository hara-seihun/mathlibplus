import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BatchO0313Claim15306

noncomputable section

private def qLog15306 (q : ℤ) : ℝ :=
  Real.log (q : ℝ)

private def qRadius15306 (q : ℤ) : ℝ :=
  Real.rpow (q : ℝ) (-(1 / 2 : ℝ))

private def verticalRoot15306 (q : ℤ) (α : ℂ) (k : ℤ) : ℂ :=
  ((-(Real.log ‖α‖) / qLog15306 q : ℝ) : ℂ) -
    Complex.I *
      (((Complex.arg α + 2 * Real.pi * (k : ℝ)) / qLog15306 q : ℝ) : ℂ)

private noncomputable def progressionMass15306 (q : ℤ) (α : ℂ) : ℝ :=
  ∑' k : ℤ,
    Real.log ‖verticalRoot15306 q α k /
      (1 - verticalRoot15306 q α k)‖

/-- Exact vertical Blaschke mass of one root progression, with the full
admitted inner-progression domain and the two singular center values removed. -/
def claim15306 : Prop :=
  ∀ (q : ℤ) (σ ϑ : ℝ),
    (2 : ℤ) ≤ q →
      let L : ℝ := qLog15306 q
      let r : ℝ := qRadius15306 q
      let α : ℂ :=
        Complex.exp (((-(σ * L) : ℝ) : ℂ) - Complex.I * (ϑ : ℂ))
      (0 < ‖α‖ ∧ ‖α‖ < r ∧ α ≠ (1 : ℂ) ∧
          α ≠ (r : ℂ) ^ 2) →
        progressionMass15306 q α =
            (1 / 2 : ℝ) * Real.log
              ((Real.cosh (σ * L) - Real.cos ϑ) /
                (Real.cosh ((1 - σ) * L) - Real.cos ϑ)) ∧
          progressionMass15306 q α =
            Real.log
              (r * ‖(1 : ℂ) - α‖ /
                ‖(r : ℂ) ^ 2 - α‖) ∧
          Real.exp (progressionMass15306 q α) =
            r * ‖(1 : ℂ) - α‖ /
              ‖(r : ℂ) ^ 2 - α‖

end

end MathlibPlus.Open.Analysis.BatchO0313Claim15306
