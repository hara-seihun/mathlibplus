import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1156Claim31657_31660

namespace MathlibPlus.Open.ResearchFormalization.R1156Claim41424

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1156

/-- Claim 41424: for each support size in the stated range, the exact
 support-indexed normalized offset carrier has the displayed count, its
 solvable subcarrier is the affine one with the displayed count, and the
 compatible state-family carrier has the displayed count. -/
def completeSupportSizeCounting_claim41424 : Prop :=
  ∀ (k : ℕ) (hk : 2 ≤ k), k ≤ 7 →
    Nat.card (NormalizedOffsetAssignments k hk) =
        Nat.choose 7 k * 7 ^ (k - 1) ∧
      Nat.card (SolvableOffsetAssignments k hk) =
        7 * Nat.choose 7 k ∧
      (∀ z : NormalizedOffsetAssignments k hk,
        assignmentIsSolvable z → assignmentIsAffine z) ∧
      Nat.card (CompatibleStateFamilies k hk) =
        84 * 7 * Nat.choose 7 k

end

end MathlibPlus.Open.ResearchFormalization.R1156Claim41424
