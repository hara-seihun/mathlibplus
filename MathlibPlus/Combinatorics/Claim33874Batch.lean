import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim33874

/-- Claim 33874: a strict common-branch weight bound excludes every branch
whose order reaches the threshold. -/
def no_common_branch_order_at_least_claim33874 : Prop :=
  ∀ {Branch : Type*} [DecidableEq Branch]
    (commonBranches : Finset Branch) (order : Branch → ℕ) (d : ℕ),
    (∑ b ∈ commonBranches, order b) < d →
      ∀ b, b ∈ commonBranches → order b < d

end MathlibPlus.Combinatorics.Claim33874
