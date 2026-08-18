import MathlibPlus.Open.ResearchFormalization.R0337

namespace MathlibPlus.Open.ResearchFormalization.R0337Claim20058_20062

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.R0337
open ProjectsResearch.TreeDeck

noncomputable section

/-- The exact positive-order chromatic deck sum on the rational span of
unlabelled trees, with its homogeneous power-sum realization. -/
def claim20058 : Prop :=
  ∀ (n : ℕ) (T : UnlabelledTree (n + 1)),
    isHomogeneousPowerSum n (chromaticDeckBasis (n + 1) T) ∧
      chromaticDeckBasis (n + 1) T =
        ∑ v : Fin (n + 1),
          treeChromaticSymmetric
            (vertexDeletedGraph (Quotient.out T).1 v)

/-- The four realized order-six witness trees have the admitted signed
chromatic-deck trade. -/
def claim20062 : Prop :=
  ∃ (T₀ T₁ T₂ T₃ : LabelledTree 6),
    T₀.1 = witnessGraph0 ∧
      T₁.1 = witnessGraph1 ∧
        T₂.1 = witnessGraph2 ∧
          T₃.1 = witnessGraph3 ∧
            ¬ graphIsomorphic T₀.1 T₁.1 ∧
              ¬ graphIsomorphic T₀.1 T₂.1 ∧
                ¬ graphIsomorphic T₀.1 T₃.1 ∧
                  ¬ graphIsomorphic T₁.1 T₂.1 ∧
                    ¬ graphIsomorphic T₁.1 T₃.1 ∧
                      ¬ graphIsomorphic T₂.1 T₃.1 ∧
                        chromaticDeckColumn (treeClass T₀) -
                            chromaticDeckColumn (treeClass T₁) +
                              chromaticDeckColumn (treeClass T₂) -
                                chromaticDeckColumn (treeClass T₃) = 0

end

end MathlibPlus.Open.ResearchFormalization.R0337Claim20058_20062
