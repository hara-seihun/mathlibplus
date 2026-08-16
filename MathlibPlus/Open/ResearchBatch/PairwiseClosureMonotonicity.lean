import MathlibPlus.Open.ResearchBatch.TranslationCocycles

namespace MathlibPlus.Open.ResearchBatch.TranslationCocycles

/-- If one additive profile code is contained in another, its pairwise closure
and every translated-difference image are contained in the corresponding
objects for the larger code. -/
def claim38965 : Prop :=
  ∀ (K₁ K₂ : AddSubgroup Profile),
    K₁ ≤ K₂ →
      pairwiseClosure K₁ ⊆ pairwiseClosure K₂ ∧
        ∀ u : H,
          difference u '' pairwiseClosure K₁ ⊆
            difference u '' pairwiseClosure K₂

end MathlibPlus.Open.ResearchBatch.TranslationCocycles
