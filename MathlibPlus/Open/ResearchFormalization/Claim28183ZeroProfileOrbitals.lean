import MathlibPlus.Open.ResearchFormalization.R1003Claim28189

namespace MathlibPlus.Open.ResearchFormalization.Claim28183

open MathlibPlus.Open.ResearchFormalization.R1003.Claim28189

noncomputable section

/-- Claim 28183: in the exact zero-profile member of the displayed R-1003
regular pair, there are 105 paired orbitals, and the actual cubing
automorphism transports every one of them through the two labelings. -/
def claim28183 : Prop :=
  ∃ e : GCoordinate ≃ EGroup,
    (∀ a b : GCoordinate,
      e (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.gMul a b) = e a * e b) ∧
      ∃ α : EGroup ≃* EGroup,
        (∀ g : GCoordinate,
          α (e g) = e (coordinateAlpha g)) ∧
          Set.ncard
              (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.pairedOrbitals
                (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.generatedPair
                  zeroProfile)) = 105 ∧
            ∃ τ : Equiv.Perm Omega,
              (∀ g : GCoordinate,
                τ (MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.lambda1 g) =
                  MathlibPlus.Open.ResearchFormalization.R1003.Claim28186.lambda2
                    zeroProfile (coordinateAlpha g)) ∧
                everyActualFusionTransported zeroProfile e α τ

end

end MathlibPlus.Open.ResearchFormalization.Claim28183
