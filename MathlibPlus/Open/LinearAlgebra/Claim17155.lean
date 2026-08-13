import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra

/-- Finite-support formalization of the Cauchy--Binet Hankel-minor statement
from claim 17155.  The finite index set is made explicit because the source's
summation index is otherwise unspecified. -/
def cauchyBinetHankel17155 : Prop :=
  ∀ (J : Finset ℕ) (a : ℕ → ℝ) (q : ℕ → ℝ),
    (∀ j ∈ J, 0 ≤ a j) →
    (∀ n : ℕ, q n = ∑ j ∈ J, a j ^ n) →
    ∀ (s r : ℕ),
      Matrix.det (fun i j : Fin r => q (s + i.1 + j.1)) =
        ∑ I ∈ J.powerset,
          if I.card = r then
            (∏ j ∈ I, a j ^ s) *
              (∏ j ∈ I, ∏ k ∈ I.filter (fun k => j < k), (a k - a j)) ^ 2
          else 0

end MathlibPlus.Open.LinearAlgebra
