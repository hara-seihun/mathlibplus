import MathlibPlus.Open.Combinatorics.TreeAttachment

namespace MathlibPlus.Open.ResearchFormalizationD0083

open MathlibPlus.Open.Combinatorics.TreeAttachment

/-- Claim 5136: once the concrete leaf-attachment map is surjective, the
same-target leaf exchanges are exactly the kernel of its rational
linearization. -/
def claim5136 : Prop :=
  ∀ (n : ℕ),
    Function.Surjective (attachmentMap n) →
      let exchangeSpace : Submodule ℚ (RootedCardSpace n) :=
        Submodule.span ℚ {z |
          ∃ x y : RootedOccurrence n,
            attachmentMap n x = attachmentMap n y ∧
              z = rootedBasis x.1 x.2 - rootedBasis y.1 y.2}
      exchangeSpace = LinearMap.ker (attachmentLinearization n)

end MathlibPlus.Open.ResearchFormalizationD0083
