import MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

namespace MathlibPlus.Open.ResearchFormalization.Claim30566

open MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

noncomputable section

/-- Every rotation-section transvection with the target coordinate convention
is supplied by the normalized relative-derivative group. -/
def rotationSectionTransvections_claim30566 : Prop :=
  ∀ (p : ℕ), Nat.Prime p → Odd p →
    ∀ h : SectionLabel, rotationSection h →
      ∀ b : ZMod p,
        ∃ d : derivativeGroup p h,
          ∀ v : V p,
            (d : Equiv.Perm (V p)) v = (v.1 + b * v.2, v.2)

end

end MathlibPlus.Open.ResearchFormalization.Claim30566
