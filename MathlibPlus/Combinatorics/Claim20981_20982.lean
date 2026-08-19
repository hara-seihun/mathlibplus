import MathlibPlus.Open.Combinatorics.UnionClosedBatch

namespace MathlibPlus.Combinatorics.R0402

open MathlibPlus.Open.Combinatorics.UnionClosedBatch

/-- Claim 20981: the canonical exact-three minimum-counterexample carrier
satisfies the `2N+3` lower bound and its equivalent `4N+7` family floor. -/
def exactThree4NPlus7LowerBound_claim20981 : Prop :=
  ∀ (n t N : ℕ) (F : Family n),
    exactThreeMinimumCounterexample t N F →
      2 * N + 3 ≤ t ∧
      F.card = 2 * t + 1 ∧
      4 * N + 7 ≤ F.card

/-- Claim 20982: after the normalized branch lower bound N>=13, the same
canonical exact-three minimum counterexample has at least 59 members. -/
def exactThreeBranchAtLeast59_claim20982 : Prop :=
  ∀ (n t N : ℕ) (F : Family n),
    exactThreeMinimumCounterexample t N F →
      13 ≤ N → 59 ≤ F.card

end MathlibPlus.Combinatorics.R0402
