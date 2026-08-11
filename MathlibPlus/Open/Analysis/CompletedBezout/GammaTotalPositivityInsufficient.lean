import Mathlib

/-!
# Gamma moment total positivity does not force completed-Bezout positivity

This registry node states the counterexample as an actual gamma density, quantifies
all generalized Hankel minors (not merely leading principal minors), and uses the
canonical factorial-scaled completed-Bezout matrix.
-/

noncomputable section

open scoped BigOperators ContDiff

namespace MathlibPlus.Open.Analysis.CompletedBezout

/-- There is a smooth gamma moment law whose generalized Hankel moment kernel is
strictly totally positive at every rank, while its rank-two completed-Bezout
determinant is positive and its rank-three determinant is negative. -/
def gammaMomentTotalPositivityInsufficient : Prop :=
  ∃ α : ℝ, 0 < α ∧
    let density (x : ℝ) : ℝ :=
      Real.rpow x (α - 1) * Real.exp (-x) / Real.Gamma α
    let moment (j : ℕ) : ℝ := Real.Gamma (α + j) / Real.Gamma α
    let scaledMoment (j : ℕ) : ℝ := moment j / (Nat.factorial (2 * j) : ℝ)
    let completedBezout (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
      fun i j => ∑ a ∈ Finset.range (min (i : ℕ) (j : ℕ) + 1),
        (i + j + 1 - 2 * a : ℕ) * scaledMoment a *
          scaledMoment (i + j + 1 - a)
    ContDiffOn ℝ ∞ density (Set.Ioi 0) ∧
      (∀ x : ℝ, 0 < x → 0 < density x) ∧
      (∀ j : ℕ,
        ∫ x in Set.Ioi (0 : ℝ), density x * x ^ j = moment j) ∧
      (∀ (N : ℕ) (rows cols : Fin N → ℕ),
        StrictMono rows → StrictMono cols →
          0 < (Matrix.of fun i j => moment (rows i + cols j)).det) ∧
      0 < (completedBezout 2).det ∧
      (completedBezout 3).det < 0

end MathlibPlus.Open.Analysis.CompletedBezout
