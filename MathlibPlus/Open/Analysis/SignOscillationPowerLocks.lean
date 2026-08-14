import Mathlib

open scoped BigOperators

namespace MathlibPlus
namespace Open
namespace Analysis

/--
Let `(lambda n)_(n >= 0)` be pairwise distinct positive real numbers and let
`(theta n)_(n >= 0)` be real numbers. If, for every nonnegative integer `q`,
`sum_n |sinh (lambda n * theta n)| * lambda n ^ q` is summable and the
corresponding signed sum is zero, then either every `theta n` is zero or both
signs occur arbitrarily far out.
-/
def nonbalancedReflectedAtomTowerSignOscillationPowerLocks
    (lambda theta : ℕ → ℝ) : Prop :=
  ((∀ n : ℕ, 0 < lambda n) ∧
      (∀ ⦃i j : ℕ⦄, i ≠ j → lambda i ≠ lambda j) ∧
      (∀ q : ℕ,
        Summable (fun n : ℕ => |Real.sinh (lambda n * theta n)| * lambda n ^ q) ∧
          (∑' n : ℕ, Real.sinh (lambda n * theta n) * lambda n ^ q) = 0)) →
    ((∀ n : ℕ, theta n = 0) ∨
      ∀ N : ℕ, ∃ m n : ℕ,
        N ≤ m ∧ N ≤ n ∧ theta m < 0 ∧ 0 < theta n)

end Analysis
end Open
end MathlibPlus
