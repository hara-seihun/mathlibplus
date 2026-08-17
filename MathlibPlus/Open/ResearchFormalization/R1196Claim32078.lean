import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1196Claim32078

noncomputable section

abbrev BranchProfile := ℕ × ℕ × ℕ

def partitionRow (r k : ℕ) : BranchProfile :=
  (r, r - k, k)

def sideProfileX (r k : ℕ) : BranchProfile :=
  (r, r - k, k - 1)

def sideProfileY (r k : ℕ) : BranchProfile :=
  (r - 1, r - k + 1, k)

def profilesDefined (r k : ℕ) : Prop :=
  1 ≤ k ∧ k + 1 ≤ r

/-- Claim 32078: the partition row and its two endpoint/transfer side
profiles are the exact natural-number triples on their applicability domain. -/
def partitionAndSideProfileFamilies_claim32078 : Prop :=
  ∀ r k : ℕ, profilesDefined r k →
    partitionRow r k = (r, r - k, k) ∧
      sideProfileX r k = (r, r - k, k - 1) ∧
        sideProfileY r k = (r - 1, r - k + 1, k)

end

end MathlibPlus.Open.ResearchFormalization.R1196Claim32078
