import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1196

noncomputable section

private abbrev BranchProfile := ℕ × ℕ × ℕ

private def partitionRow (r k : ℕ) : BranchProfile :=
  (r, r - k, k)

private def sideProfileX (r k : ℕ) : BranchProfile :=
  (r, r - k, k - 1)

private def sideProfileY (r k : ℕ) : BranchProfile :=
  (r - 1, r - k + 1, k)

private def profilesDefined (r k : ℕ) : Prop :=
  1 ≤ k ∧ k + 1 ≤ r

private def p3Excess (d : BranchProfile) : ℤ :=
  (Nat.choose d.1 2 : ℤ) +
    (Nat.choose d.2.1 2 : ℤ) +
    (Nat.choose d.2.2 2 : ℤ)

private def exactXYGradeIdentity (r k : ℕ) : Prop :=
  profilesDefined r k →
    p3Excess (sideProfileX r k) = p3Excess (sideProfileY r k) ∧
      p3Excess (sideProfileX r k) -
          p3Excess (partitionRow r (k + 1)) =
        (r : ℤ) - 3 * (k : ℤ)

/-- Claim 32080: the exact P3-excess grades of the two side profiles and the
next partition row differ by the signed gap r-3k. -/
def claim32080 : Prop :=
  ∀ r k : ℕ, exactXYGradeIdentity r k

/-- Claim 41851: the same exact profile-grade identity under its duplicate
admitted claim identity. -/
def claim41851 : Prop :=
  ∀ r k : ℕ, exactXYGradeIdentity r k

end
end MathlibPlus.Open.ResearchFormalization.R1196
