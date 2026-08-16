import Mathlib

open Filter Asymptotics

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The Levy numerator in the O-0321 counterexample, on its asserted positive half-line. -/
def levyNumeratorO0321 (x : ℝ) : ℝ :=
  Real.exp (-x) * (3 + 2 * Real.cos x) + 1 / (2 * Real.sinh x)

/-- Complete monotonicity on the positive half-line. -/
def completelyMonotoneOnPositive (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ f (Set.Ioi (0 : ℝ)) ∧
    ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

/-- The Levy numerator is decreasing but fails complete monotonicity, with the
fixed-order derivative asymptotic and the adverse phases from O-0321. -/
def levyNumeratorNotCompletelyMonotone : Prop :=
  StrictAntiOn levyNumeratorO0321 (Set.Ioi (0 : ℝ)) ∧
  (∀ n : ℕ,
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ =>
        (-1 : ℝ) ^ n * iteratedDeriv n levyNumeratorO0321 x -
          Real.exp (-x) *
            (4 + 2 * (Real.sqrt 2) ^ n *
              Real.cos (x - (n : ℝ) * Real.pi / 4)))
      (fun x : ℝ => (3 : ℝ) ^ n * Real.exp (-3 * x))) ∧
  (∀ n : ℕ, 3 ≤ n →
    ∀ R : ℝ,
      ∃ m : ℕ,
        let x : ℝ :=
          Real.pi + (n : ℝ) * Real.pi / 4 + 2 * Real.pi * (m : ℝ)
        R < x ∧
          (-1 : ℝ) ^ n * iteratedDeriv n levyNumeratorO0321 x < 0) ∧
  ¬ completelyMonotoneOnPositive levyNumeratorO0321

end
end MathlibPlus.Open.Analysis
