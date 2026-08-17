import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

namespace MathlibPlus.Open.ResearchFormalization.R1118FixedQuadraticTransporter29097

noncomputable section

open MathlibPlus.Open.ResearchFormalizationBatch_01a000eb

/-- Claim 29097: the displayed quadratic transporter, right-translation
subgroup, and generated pair group form the exact fixed carrier. -/
def claim29097 : Prop :=
  ∀ (f : F3Square → F3) (Fmap : F3Square → F3Cube),
    (∀ (z : F3) (x : F3Square) (u : F3Cube),
      rankFiveQuadraticTransporterPerm f Fmap (z, (x, u)) =
        (z + f x + dot3 (Fmap x) u,
          (x, u + quadraticIncrement x))) ∧
    (∀ t : rankFiveTranslationGroup,
      (t.1 : Equiv.Perm RankFiveE) ∈ rankFivePairGroup f Fmap) ∧
    (∀ t : conjugatedTranslationGroup rankFiveTranslationGroup
        (rankFiveQuadraticTransporterPerm f Fmap),
      (t.1 : Equiv.Perm RankFiveE) ∈ rankFivePairGroup f Fmap) ∧
    (∀ H : Subgroup (Equiv.Perm RankFiveE),
      rankFiveTranslationGroup ≤ H →
        conjugatedTranslationGroup rankFiveTranslationGroup
            (rankFiveQuadraticTransporterPerm f Fmap) ≤ H →
          rankFivePairGroup f Fmap ≤ H)

end

end MathlibPlus.Open.ResearchFormalization.R1118FixedQuadraticTransporter29097
