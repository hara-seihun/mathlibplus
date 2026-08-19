import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim49598

open scoped BigOperators

/-- The exact level-one decoy contribution for the admitted scalable family:
rank `r=1,...,n` contributes `r/(16 n^2)`. -/
def levelOneRankContribution (n : ℕ) : ℚ :=
  ∑ r : Fin n, ((r.val + 1 : ℕ) : ℚ) / (16 * (n : ℚ) ^ 2)

/-- The exact level-two rank contribution on the two main branches. -/
def levelTwoRankContribution (n : ℕ) : ℚ :=
  let wScore : ℚ := 1 / (8 * (n : ℚ) ^ 2)
  let goodBranch : ℚ :=
    1 / 2 + ∑ r : Fin n, ((r.val + 2 : ℕ) : ℚ) * wScore
  let badBranch : ℚ :=
    ∑ r : Fin n, ((r.val + 1 : ℕ) : ℚ) * wScore
  (goodBranch + badBranch) / 2

/-- The actual root rank-potential sum for this two-level family. -/
def rootRankPotential (n : ℕ) : ℚ :=
  levelOneRankContribution n + levelTwoRankContribution n

/-- Claim 49598: the finite decoy sums evaluate to the two displayed
contributions, and their sum is the exact initial rank potential. -/
def claim49598_exactInitialRankPotential : Prop :=
  ∀ n : ℕ, 0 < n →
    levelOneRankContribution n = ((n + 1 : ℕ) : ℚ) / (32 * (n : ℚ)) ∧
      levelTwoRankContribution n = 5 / 16 + 1 / (8 * (n : ℚ)) ∧
      rootRankPotential n = ((11 * n + 5 : ℕ) : ℚ) / (32 * (n : ℚ))

end MathlibPlus.Open.ResearchFormalization.Claim49598
