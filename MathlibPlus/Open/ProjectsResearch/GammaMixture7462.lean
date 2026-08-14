import Mathlib

namespace MathlibPlus.Open.ProjectsResearch

open MeasureTheory

/-- The bilateral theta source appearing in the admitted realization of the
completed xi-function. -/
noncomputable def thetaSource (u : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 0 < n then
      (4 * Real.pi ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
          6 * Real.pi * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
        Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
    else 0

/-- `X(λ) = ξ(1/2 + λ)` as supplied by the positive bilateral theta source. -/
noncomputable def xiHalfSource (r : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (r * u) * thetaSource |u|

/-- No nonzero positive measure on `(0,∞)` has the one-sided Gamma(2)
transform claimed for the xi quotient. -/
def oneSidedPositiveGammaTwoMixtureContradiction : Prop :=
  ¬ ∃ M : Measure (Set.Ioi (0 : ℝ)),
      M ≠ 0 ∧
        ∀ s : ℝ, 0 < s →
          xiHalfSource s / xiHalfSource 0 =
            ∫ t : Set.Ioi (0 : ℝ), (s + (t : ℝ))⁻¹ ^ 2 ∂M

end MathlibPlus.Open.ProjectsResearch
