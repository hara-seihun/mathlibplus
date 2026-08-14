import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.HeatMomentHierarchy

open scoped BigOperators

/-- The nonlinear heat-moment hierarchy stated for a real-valued moment
trajectory `q`, with the dot notation represented by `HasDerivAt`. -/
def nonlinearHeatMomentHierarchy (q : ℝ → ℕ → ℝ) : Prop :=
  ∀ (t : ℝ) (m : ℕ),
    1 ≤ m →
      HasDerivAt
        (fun τ : ℝ => q τ m)
        (-(m : ℝ) *
          (((4 * m + 2 : ℕ) : ℝ) * q t (m + 1) -
            4 * (Finset.sum (Finset.Icc 1 m)
              (fun i => q t i * q t (m + 1 - i)))))
        t

/-- The first three displayed equations of the same hierarchy. -/
def firstThreeNonlinearHeatMomentEquations (q : ℝ → ℕ → ℝ) : Prop :=
  ∀ t : ℝ,
    HasDerivAt (fun τ : ℝ => q τ 1)
      (4 * (q t 1) ^ 2 - 6 * q t 2) t ∧
    HasDerivAt (fun τ : ℝ => q τ 2)
      (16 * q t 1 * q t 2 - 20 * q t 3) t ∧
    HasDerivAt (fun τ : ℝ => q τ 3)
      (24 * q t 1 * q t 3 + 12 * (q t 2) ^ 2 - 42 * q t 4) t

end MathlibPlus.Open.ResearchFormalizationBatch.HeatMomentHierarchy
