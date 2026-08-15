import Mathlib

namespace MathlibPlus.Open.Formalization

open scoped BigOperators

/-- The local forbidden action η_j(λ). -/
noncomputable def localForbiddenAction (a : ℕ → ℝ) (lam : ℝ) (j : ℕ) : ℝ :=
  Real.log ((lam - a (j + 1)) / a j)

/-- The accumulated forbidden action I_{k,r}(λ). -/
noncomputable def accumulatedForbiddenAction
    (a : ℕ → ℝ) (lam : ℝ) (k r : ℕ) : ℝ :=
  Finset.sum (Finset.Icc (k + 1) r) (fun j => localForbiddenAction a lam j)

/-- The suffix row-sum barrier on the indices following an interface. -/
def suffixRowSumBarrier
    (N : ℕ) (a : ℕ → ℝ) (lam : ℝ) (k : ℕ) : Prop :=
  ∀ j : ℕ, k + 1 ≤ j → j < N → lam ≥ a j + a (j + 1)

/--
Local and accumulated forbidden actions for a positive zero-diagonal Jacobi
coefficient sequence: η_j(λ) is the logarithmic local action and
I_{k,r}(λ) is its accumulated sum; the suffix row-sum barrier makes both
nonnegative.
-/
def claim8766 (N : ℕ) (a : ℕ → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧
    a 0 = 0 ∧
    a N = 0 ∧
    (∀ j : ℕ, 1 ≤ j → j < N → 0 < a j) ∧
    (∀ k : ℕ, k < N - 1 →
      suffixRowSumBarrier N a lam k →
        (∀ j : ℕ, k + 1 ≤ j → j < N →
          0 ≤ localForbiddenAction a lam j) ∧
        (∀ r : ℕ, k < r → r < N →
          0 ≤ accumulatedForbiddenAction a lam k r))

end MathlibPlus.Open.Formalization
