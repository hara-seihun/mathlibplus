import Mathlib
import MathlibPlus.Open.Analysis.Claim11285
import MathlibPlus.Open.ResearchFormalizationBatch.WidderFiniteDepth

open scoped BigOperators
open MeasureTheory
open MathlibPlus.Open.ResearchFormalizationBatch

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The real positive-axis carrier descended from the independently specified
counterfeit polynomial of Claim 11285. -/
noncomputable def counterfeitHY11286 (x : ℝ) : ℝ :=
  (MathlibPlus.Analysis.Claim11285.descendedLogDerivative (x : ℂ)).re

/-- Claim 11286: the independent counterfeit carrier has the displayed
nonnegative Laplace density and is completely monotone on the positive axis. -/
def claim11286 : Prop :=
  (∀ t : ℝ, 0 ≤ t →
    0 ≤ 4 * Real.exp (-t) * (1 + Real.cos t)) ∧
  (∀ x : ℝ, 0 < x →
    counterfeitHY11286 x =
      ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-x * t) *
          (4 * Real.exp (-t) * (1 + Real.cos t))) ∧
  (∀ x : ℝ, 0 < x →
    counterfeitHY11286 x =
      shiftedDescendedLogDerivative 2 (3 / 4 : ℝ) 1 x) ∧
  (∀ (m : ℕ) (x : ℝ), 0 < x →
    0 ≤ (-1 : ℝ) ^ m * iteratedDeriv m counterfeitHY11286 x)

end MathlibPlus.Open.Analysis
