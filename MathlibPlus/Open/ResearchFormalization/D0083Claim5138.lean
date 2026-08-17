import MathlibPlus.Open.Combinatorics.TreeAttachment

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.D0083Claim5138

open MathlibPlus.Open.Combinatorics.TreeAttachment

noncomputable section

noncomputable def withinCardMomentVector_claim5138
    (n : ℕ) (Feature : Type*)
    (weight : Feature → RootedOccurrence (n - 1) → ℚ)
    (hweight :
      ∀ f : Feature, ∀ C : UnlabelledTree (n - 1),
        ∀ e : (treeRepresentative C).1 ≃g (treeRepresentative C).1,
          ∀ v : Vertex (n - 1),
            weight f (C, e v) = weight f (C, v))
    (f : Feature) (C : UnlabelledTree (n - 1)) :
    RootedCardSpace (n - 1) :=
  ∑ v : Vertex (n - 1),
    weight f (C, v) • rootedBasis C v

noncomputable def withinCardMomentSubspace_claim5138
    (n : ℕ) (Feature : Type*) [Fintype Feature]
    (weight : Feature → RootedOccurrence (n - 1) → ℚ)
    (hweight :
      ∀ f : Feature, ∀ C : UnlabelledTree (n - 1),
        ∀ e : (treeRepresentative C).1 ≃g (treeRepresentative C).1,
          ∀ v : Vertex (n - 1),
            weight f (C, e v) = weight f (C, v)) :
    Submodule ℚ (RootedCardSpace (n - 1)) :=
  Submodule.span ℚ
    (Set.range fun p : Feature × UnlabelledTree (n - 1) =>
      withinCardMomentVector_claim5138 n Feature weight hweight p.1 p.2)

end
end MathlibPlus.Open.ResearchFormalization.D0083Claim5138
