import MathlibPlus.Open.ResearchFormalization.R1156Claim31657_31660

namespace MathlibPlus.Open.ResearchFormalization.R1156CompleteClassification31662

open MathlibPlus.Open.ResearchFormalization.R1156
open scoped BigOperators

noncomputable section

/-- Claim 31662: the exact normalized-offset carriers have no solvable
nonaffine assignment at any support size from two through seven, and their
complete cardinalities sum to 299586. -/
def claim31662 : Prop :=
  (Finset.Icc 2 7).sum (fun k =>
      Nat.choose 7 k * 7 ^ (k - 1)) = 299586 ∧
    ∀ (k : ℕ) (hk : 2 ≤ k),
      k ≤ 7 →
        Nat.card (NormalizedOffsetAssignments k hk) =
            Nat.choose 7 k * 7 ^ (k - 1) ∧
          ∀ z : NormalizedOffsetAssignments k hk,
            assignmentIsSolvable z → assignmentIsAffine z

end

end MathlibPlus.Open.ResearchFormalization.R1156CompleteClassification31662
