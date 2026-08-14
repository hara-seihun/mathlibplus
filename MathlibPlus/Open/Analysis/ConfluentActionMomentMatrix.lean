import Mathlib

namespace MathlibPlus.Open.Analysis

/--
Claim 17657.  The rows are indexed by action/derivative-order pairs, sorted
lexicographically, and each action carries the initial segment of derivative
orders `0, ..., r - 1`.  The displayed entry formula is the Hermite/confluent
replacement of a repeated action row by successive action derivatives.
-/
def confluentActionMomentMatrix_claim17657 : Prop :=
  ∀ (N : ℕ)
    (m : Fin N → ℝ → ℝ)
    (lambda : Fin N → ℝ)
    (a : Fin N → ℕ),
    (∀ x : ℝ, ∀ k : ℕ,
      (∃ i : Fin N, lambda i = x ∧ a i = k) ↔
        k < Fintype.card {i : Fin N // lambda i = x}) →
      (∀ i j : Fin N, i < j →
        lambda i < lambda j ∨ (lambda i = lambda j ∧ a i < a j)) →
        ∃! M : Matrix (Fin N) (Fin N) ℝ,
          ∀ i j : Fin N,
            M i j = iteratedDeriv (a i) (m j) (lambda i)

end MathlibPlus.Open.Analysis
