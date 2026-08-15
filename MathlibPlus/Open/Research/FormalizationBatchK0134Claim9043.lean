import MathlibPlus.Open.ResearchFormalizationBatch_01a000ea_dbd6_7a56_af5f_ee57b3e2d981

open Filter
open MeasureTheory

namespace MathlibPlus.Open.Research.FormalizationBatchK0134Claim9043

open MathlibPlus.Open.ResearchFormalizationBatch_01a000ea_dbd6_7a56_af5f_ee57b3e2d981

/-- The first-shell phase's negative second derivative in the saddle variable. -/
noncomputable def negativePhaseCurvature9043 (x u : ℝ) : ℝ :=
  -deriv (fun v : ℝ => deriv (fun z : ℝ => firstShellPhase x z) v) u

/-- Claim 9043: saddle variance asymptotic and exact negative phase curvature. -/
def saddleVarianceAsymptotic9043 : Prop :=
  (∃ C : ℝ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop,
      |firstShellLogVariance x -
          1 / (2 * x * (1 + lambertW0 (2 * x / Real.pi)))| ≤
        C * (1 / (x * lambertW0 (2 * x / Real.pi) ^ 2) + 1 / x ^ 2)) ∧
    (∀ x : ℝ, 1 ≤ x →
      ∃! u : ℝ,
        0 < u ∧
          2 * x / u + 1 / 2 = 2 * Real.pi * Real.exp (2 * u)) ∧
    (∀ x : ℝ, 1 ≤ x → ∀ u : ℝ, 0 < u →
      2 * x / u + 1 / 2 = 2 * Real.pi * Real.exp (2 * u) →
      negativePhaseCurvature9043 x u =
        2 * x / u ^ 2 * (1 + 2 * u + u ^ 2 / (2 * x)))

end MathlibPlus.Open.Research.FormalizationBatchK0134Claim9043
