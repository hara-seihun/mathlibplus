import MathlibPlus.Open.ResearchFormalization.BatchD0083Claim5141

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.D0083Claim5140

open MathlibPlus.Open.Combinatorics.TreeAttachment
open MathlibPlus.Open.ResearchFormalization.D0083Claim5141

noncomputable section

/-- The weighted grafting family on the actual invariant feature carrier: its
basis action is attachment of the within-card moment vector, and its range is
exactly the attachment image of the moment subspace. -/
def weightedGraftingFamily_claim5140 : Prop :=
  ∀ (n : ℕ) (h : 1 ≤ n)
    (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ),
    automorphismInvariantWeight n Feature weight →
      let G := weightedGraftingMap n h Feature weight
      (∀ f : Feature, ∀ C : UnlabelledTree (n - 1),
        G (Finsupp.single (f, C) 1) =
          attachmentLinearizationAt n h
            (momentVector n Feature weight f C)) ∧
        LinearMap.range G =
          Submodule.map (attachmentLinearizationAt n h)
            (momentSpace n Feature weight)

end

end MathlibPlus.Open.ResearchFormalization.D0083Claim5140
