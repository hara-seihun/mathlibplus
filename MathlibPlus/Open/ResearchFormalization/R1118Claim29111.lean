import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

namespace MathlibPlus.Open.ResearchFormalization.R1118Claim29111

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

/-- Claim 29111: the exact five-parameter atlas normalizer preserves the
    displayed translation group and its composite with q conjugates that
    group to the displayed q-conjugate. -/
def fiveParameterLinearNormalizerFamily_claim29111 : Prop :=
  ∀ (param : Fin 5 → F3)
    (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    atlasNormalizer param ∈
        Subgroup.normalizer rankFiveTranslationGroup ∧
      conjugatedTranslationGroup rankFiveTranslationGroup
          (atlasComposite param f Fmap) =
        conjugatedTranslationGroup rankFiveTranslationGroup
          (rankFiveQuadraticTransporterPerm f Fmap)

end MathlibPlus.Open.ResearchFormalization.R1118Claim29111
