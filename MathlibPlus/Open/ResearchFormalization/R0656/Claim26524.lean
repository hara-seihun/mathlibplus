import MathlibPlus.Open.ResearchFormalization.R0656.Claim26525

namespace MathlibPlus.Open.ResearchFormalization.R0656

noncomputable section

/-- The exact degree-two scalar space in the reviewed labelled carrier. -/
def degreeTwoScalarSpace_claim26524 : Submodule ℚ A2 :=
  Submodule.span ℚ ({a2_s_squared, a2_q} : Set A2)

/-- The exact degree-three scalar space in the reviewed labelled carrier. -/
def degreeThreeScalarSpace_claim26524 : Submodule ℚ A3 :=
  Submodule.span ℚ
    ({a3_s_cubed, a3_s_q, a3_p_sub_c, a3_c_sub_se} : Set A3)

/-- Claim 26524: the complete degree-two and degree-three scalar carriers are
spanned by the four displayed scalar directions, with dimensions two and four. -/
def completeDegreeTwoThreeScalarSpaces_claim26524 : Prop :=
  degreeTwoScalarSpace_claim26524 = ⊤ ∧
    degreeThreeScalarSpace_claim26524 = ⊤ ∧
      Module.finrank ℚ degreeTwoScalarSpace_claim26524 = 2 ∧
        Module.finrank ℚ degreeThreeScalarSpace_claim26524 = 4

end

end MathlibPlus.Open.ResearchFormalization.R0656
