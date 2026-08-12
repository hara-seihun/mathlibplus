import Mathlib

namespace MathlibPlus.Open.Analysis

/--
The exact fixed-range variational claim from admitted claim 1557.  The displayed
functional is the source's `N_{1,2}`; no endpoint-vanishing condition is added.
-/
def exactNormMinimizer_1557 : Prop :=
  let N : (ℝ → ℝ) → ℝ := fun w =>
    (1 / (2 * Real.pi)) *
      (w 2 / 2 + w 1
        + ∫ u in (1 : ℝ)..2, w u / u
        + ∫ u in (1 : ℝ)..2, |deriv w u| / u)
  ∀ w : ℝ → ℝ,
    ContDiffOn ℝ 1 w (Set.Icc (1 : ℝ) 2) →
    (∀ u ∈ Set.Icc (1 : ℝ) 2, 0 ≤ w u) →
    (∫ u in (1 : ℝ)..2, w u) = 1 →
    N w ≥ (3 / 2 + Real.log 2) / (2 * Real.pi) ∧
      (N w = (3 / 2 + Real.log 2) / (2 * Real.pi) ↔
        ∀ u ∈ Set.Icc (1 : ℝ) 2, w u = 1)

end MathlibPlus.Open.Analysis
