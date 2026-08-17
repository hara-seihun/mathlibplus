import MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

namespace MathlibPlus.Open.ResearchFormalization.Batch_52e47c1f_Frobenius21Support

open MathlibPlus.Open.ResearchFormalizationBatch.Frobenius21Claims

/-- Claim 39594: the nonlinear chart support is disjoint from its left
stabilizer, and every chart indexed by that stabilizer is a fibre
translation. -/
def claim39594 : Prop :=
  ∀ (π : Frobenius21 → Equiv.Perm F5),
    π 1 = 1 →
      let N := nonlinearSupport π
      let L := leftStabilizerSet N
      N ∩ L = ∅ ∧
        ∀ g, g ∈ L → isFibreTranslation (π g)

end MathlibPlus.Open.ResearchFormalization.Batch_52e47c1f_Frobenius21Support
