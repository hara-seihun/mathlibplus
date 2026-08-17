import MathlibPlus.Open.Research.FormalizationBatch.R1220

namespace MathlibPlus.Open.Research.R1220

noncomputable section

noncomputable def ciDefectMultiplicity (S : ConnectionSet) : ℕ :=
  Set.ncard
    {q : Quotient (MulAction.orbitRel (G90 ≃* G90) (valencySlice (valency S))) |
      ∃ T : valencySlice (valency S),
        Quotient.mk (MulAction.orbitRel (G90 ≃* G90) (valencySlice (valency S))) T = q ∧
          graphIsomorphic T.1 S}

def claim30274 : Prop :=
  (∀ (φ : G90 ≃* G90) (S : ConnectionSet),
    automorphismImage φ (connectionComplement S) =
      connectionComplement (automorphismImage φ S)) ∧
  (∀ S T : ConnectionSet, graphIsomorphic S T →
    graphIsomorphic (connectionComplement S) (connectionComplement T)) ∧
  (∀ S : ConnectionSet,
    valency (connectionComplement S) = 89 - valency S) ∧
  (∀ S : ConnectionSet,
    ciDefectMultiplicity (connectionComplement S) = ciDefectMultiplicity S)

end
end MathlibPlus.Open.Research.R1220
