import MathlibPlus.Open.ResearchFormalization.R1404CarryAtlas

namespace MathlibPlus.Open.ResearchFormalization.R1404Claim38674

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1404

/-- Claim 38674: on the exact degree-27 carry atlas, every normalized scalar
    switch at a base-pair position gives a second regular copy from the
    conjugation of the regular translation copy with the displayed defining
    transporter. -/
def centralLineCarryModel_claim38674 : Prop :=
  ∀ (p : BasePosition) (g : BasePoint → ZMod 3),
    normalizedCarry g →
      regularPermutationSubgroup regularAtlasSubgroup ∧
        regularPermutationSubgroup (secondRegularCopy p g) ∧
          conjugatedSubgroup
              (definingTransporter (positionRepresentative p) g)
              regularAtlasSubgroup =
            secondRegularCopy p g

end

end MathlibPlus.Open.ResearchFormalization.R1404Claim38674
