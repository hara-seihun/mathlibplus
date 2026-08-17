import MathlibPlus.Open.ResearchFormalizationBatch_01a000fa_cafc_7f26_afad_440b9a41e3b3

namespace MathlibPlus.Open.ResearchFormalization.R1350

open MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 41255: the Record-8 conclusion is quantified over an arbitrary
family of permutations.  Apart from the identity normalization, its only
premises are the derivative invariance, the two inverse-closure conditions,
and the exponent-two/exponent-three hypotheses. -/
def claim41255 : Prop :=
  ∀ (V H : Type*) [Fintype V] [AddCommGroup V]
    [Fintype H] [Group H],
    exponentTwo (V := V) →
      exponentThree (H := H) →
        ∀ (q : H → Equiv.Perm V),
          q 1 = Equiv.refl V →
            ∀ S : Set (V × H),
              normalizedRelativeDerivativeInvariant q S →
                inverseClosed S →
                  inverseClosed (presentationMap q '' S) →
                    presentationMap q '' S = S

end MathlibPlus.Open.ResearchFormalization.R1350
