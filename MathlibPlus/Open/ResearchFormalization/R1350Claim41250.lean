import MathlibPlus.Open.ResearchFormalizationBatch_01a000fa_cafc_7f26_afad_440b9a41e3b3

namespace MathlibPlus.Open.ResearchFormalization.R1350

open MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 41250: in the normalized arbitrary identity-base fibre context,
exponent-two source and target inverse closure identify the inverse-section
image with the common image of the original section. -/
def claim41250 : Prop :=
  ∀ (V H : Type*) [AddCommGroup V] [Group H],
    ∀ (q : H → Equiv.Perm V) (S : Set (V × H)),
      exponentTwo (V := V) →
        q 1 = Equiv.refl V →
          inverseClosed S →
            inverseClosed (presentationMap q '' S) →
              ∀ h : H,
                q (h⁻¹) '' fibre S (h⁻¹) = q h '' fibre S h ∧
                  let X := fibre S h
                  q (h⁻¹) '' X = q h '' X

end MathlibPlus.Open.ResearchFormalization.R1350
