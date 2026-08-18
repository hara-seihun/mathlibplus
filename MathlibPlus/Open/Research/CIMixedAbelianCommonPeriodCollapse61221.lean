import MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160

namespace MathlibPlus.Open.Research.CIMixedAbelianCommonPeriodCollapse61221

noncomputable section

open MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160

abbrev F2 := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.F2
abbrev F3 := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.F3
abbrev A := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.A
abbrev B := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.B
abbrev G := MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.G
abbrev LinearAutomorphism :=
  MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.LinearAutomorphism
abbrev IncidenceComponent :=
  MathlibPlus.Open.Research.CIMixedAbelianRepresentationChart61160.IncidenceComponent

/-- The arbitrary pointed block-preserving permutation in the claim. -/
def blockChart (p : B → (A ≃ A)) (σ : B ≃ B) : G ≃ G :=
  (Equiv.prodComm A B).trans
    ((Equiv.sigmaEquivProd B A).symm.trans
      ((Equiv.sigmaCongr σ (fun b => p b)).trans
        ((Equiv.sigmaEquivProd B A).trans (Equiv.prodComm B A))))

/-- The origin-translation chart obtained from the values `c_b = p_b(0)`. -/
def originTranslationChart (p : B → (A ≃ A)) (σ : B ≃ B) : G ≃ G :=
  (Equiv.prodComm A B).trans
    ((Equiv.sigmaEquivProd B A).symm.trans
      ((Equiv.sigmaCongr σ (fun b => Equiv.addRight ((p b) 0))).trans
        ((Equiv.sigmaEquivProd B A).trans (Equiv.prodComm B A))))

/-- Periodicity of every target fibre by an additive subgroup of the binary fibre. -/
def fiberPeriodic (P : AddSubgroup A) (T : Set G) : Prop :=
  ∀ (a u : A) (h : B),
    u ∈ P → ((a, h) ∈ T ↔ (a + u, h) ∈ T)

/-- The target connection set belonging to one incidence component. -/
def targetComponentSet {f : G ≃ G} (C : IncidenceComponent f) : Set G :=
  targetConnectionSet ({C} : Set (IncidenceComponent f))

/-- The common-period hypotheses for a selected collection of the complete
inverse-atom incidence components of the arbitrary block chart. -/
def commonPeriodCondition
    (p : B → (A ≃ A)) (σ : B ≃ B)
    (K : Set (IncidenceComponent (blockChart p σ))) : Prop :=
  ∀ C : IncidenceComponent (blockChart p σ),
    C ∈ K →
      ∃ P : AddSubgroup A,
        fiberPeriodic P (targetComponentSet C) ∧
          ∀ (a : A) (b : B),
            (p b) a - a - (p b) 0 ∈ P

/-- The ordinary identity-free inverse-closed Cayley-CI defect excluded by
one product-linear transporter. -/
def ordinaryUndirectedCayleyCIDefect
    (f : G ≃ G) (S T : Set G) : Prop :=
  identityFree S ∧ inverseClosed S ∧
    identityFree T ∧ inverseClosed T ∧
    ordinaryGraphIsomorphism f S T ∧
    ¬ ∃ α : LinearAutomorphism,
      groupAutomorphismAction α '' S = T

/-- Claim 61221: for an arbitrary pointed block-preserving permutation on
`F₂⁴ × F₃²`, a selected componentwise common period makes the origin chart
carry the same Cayley relation, and the complete translation-chart shadow
supplies one product-linear automorphism for the selected union. -/
def claim_61221 : Prop :=
  ∀ (p : B → (A ≃ A)) (σ : B ≃ B),
    (p 0) 0 = 0 →
    σ 0 = 0 →
    ∀ K : Set (IncidenceComponent (blockChart p σ)),
      commonPeriodCondition p σ K →
      let S := sourceConnectionSet K
      let T := targetConnectionSet K
      identityFree S ∧
        inverseClosed S ∧
        identityFree T ∧
        inverseClosed T ∧
        ordinaryGraphIsomorphism (blockChart p σ) S T ∧
        ordinaryGraphIsomorphism (originTranslationChart p σ) S T ∧
        ∃ α : LinearAutomorphism,
          groupAutomorphismAction α '' S = T ∧
        ¬ ordinaryUndirectedCayleyCIDefect
          (blockChart p σ) S T

end
end MathlibPlus.Open.Research.CIMixedAbelianCommonPeriodCollapse61221
