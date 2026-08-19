import MathlibPlus.Open.ResearchFormalization.R1003Claim28189

namespace MathlibPlus.Open.ResearchFormalization.R1003.Claim28187

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R1003.Claim28186

abbrev HCoordinate := MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.HCoordinate
abbrev GCoordinate := MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.GCoordinate
abbrev Omega := MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.Omega
abbrev EGroup := MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.EGroup

/-- Pointwise transport of one paired orbital, including the prescribed
source-to-target labeling direction. -/
def orbitalTransported
    (t : HCoordinate → ZMod 7)
    (e : GCoordinate ≃ EGroup)
    (α : EGroup ≃* EGroup)
    (τ : Equiv.Perm Omega)
    (O : Set (Omega × Omega)) : Prop :=
  O ∈ pairedOrbitals (generatedPair t) →
    MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.pairImage τ O = O ∧
      Set.image α
          (Set.image e
            (MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.labelingConnectionSet
              lambda1 O)) =
        Set.image e
          (MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.labelingConnectionSet
            (lambda2 t) O)

/-- Claim 28187: the single cubing automorphism, represented on the named
`E(C₃₅,8)` group by the displayed coordinate map, individually transports all
18 paired orbitals for each of the 234 nonzero one-support profiles. -/
def claim28187 : Prop :=
  ∃ e : GCoordinate ≃ EGroup,
    (∀ a b : GCoordinate, e (gMul a b) = e a * e b) ∧
      ∃ α : EGroup ≃* EGroup,
        (∀ g : GCoordinate,
          α (e g) = e
            (MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.coordinateAlpha g)) ∧
          Nat.card {t : HCoordinate → ZMod 7 //
            nonzeroNormalizedOneSupport t} = 234 ∧
          ∀ t : HCoordinate → ZMod 7,
            nonzeroNormalizedOneSupport t →
              Set.ncard (pairedOrbitals (generatedPair t)) = 18 ∧
                ∃ τ : Equiv.Perm Omega,
                  (∀ g : GCoordinate,
                    τ (lambda1 g) =
                      lambda2 t
                        (MathlibPlus.Open.ResearchFormalization.R1003.Claim28189.coordinateAlpha g)) ∧
                    ∀ O : Set (Omega × Omega),
                      orbitalTransported t e α τ O

end

end MathlibPlus.Open.ResearchFormalization.R1003.Claim28187
