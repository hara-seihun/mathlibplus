import MathlibPlus.Open.ResearchFormalization.R1404CarryAtlas

namespace MathlibPlus.Open.ResearchFormalization.R1404AlternateTransporter38679

open MathlibPlus.Open.ResearchFormalization.R1404

noncomputable section

/-- Claim 38679: every exact defining-transporter miss row has an
origin-fixing conjugator in the same generated directed binary two-closure. -/
def claim38679 : Prop :=
  ∀ row : atlasFailureRows,
    alternateOriginFixingConjugator row.1.1 row.1.2

end

end MathlibPlus.Open.ResearchFormalization.R1404AlternateTransporter38679
