import MathlibPlus.Open.ResearchFormalization.R1196Claim32078

namespace MathlibPlus.Open.ResearchFormalization.R1196Claim41849

open MathlibPlus.Open.ResearchFormalization.R1196Claim32078

/-- Claim 41849: the partition row and the two displayed side-profile
families on their exact applicability domain. -/
def claim41849 : Prop :=
  ∀ r k : ℕ, profilesDefined r k →
    partitionRow r k = (r, r - k, k) ∧
      sideProfileX r k = (r, r - k, k - 1) ∧
        sideProfileY r k = (r - 1, r - k + 1, k)

end MathlibPlus.Open.ResearchFormalization.R1196Claim41849
