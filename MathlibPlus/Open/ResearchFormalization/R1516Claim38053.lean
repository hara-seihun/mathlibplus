import MathlibPlus.Open.ResearchFormalization.R1516Claim38054

namespace MathlibPlus.Open.ResearchFormalization.R1516Claim38053

noncomputable section

private def rightRegularSubgroup {X : Type*} [Group X] :
    Subgroup (Equiv.Perm X) :=
  Subgroup.closure (Set.range (fun x : X => Equiv.mulRight x))

private def productAutomorphism {A B : Type*} [Group A] [Group B]
    (Φ : A × B ≃* A × B) : Equiv.Perm (A × B) :=
  Φ.toEquiv

private def conjugatedRowMap {A B : Type*} [Group A] [Group B]
    (f : Equiv.Perm (A × B)) (Φ : A × B ≃* A × B) :
    Equiv.Perm (A × B) :=
  ((productAutomorphism Φ).trans f).trans (productAutomorphism Φ).symm

private def conjugatedDerivativeGroup
    {A B : Type*} [Group A] [Group B]
    (f : Equiv.Perm (A × B)) (Φ : A × B ≃* A × B) :
    Subgroup (Equiv.Perm (A × B)) :=
  MathlibPlus.Open.ResearchFormalization.R1516Claim38054.normalizedDerivativeSubgroup
    (conjugatedRowMap f Φ)

private def derivativeGroupConjugateBy
    {A B : Type*} [Group A] [Group B]
    (f : Equiv.Perm (A × B)) (Φ : A × B ≃* A × B) : Prop :=
  conjugatedDerivativeGroup f Φ =
    (MathlibPlus.Open.ResearchFormalization.R1516Claim38054.normalizedDerivativeSubgroup f).map
      (MulAut.conj (productAutomorphism Φ).symm).toMonoidHom

def regularDerivativeNaturality_claim38053 : Prop :=
  ∀ {A B : Type*} [Fintype A] [Fintype B] [Group A] [Group B]
    (Φ : A × B ≃* A × B) (f : Equiv.Perm (A × B)),
    (rightRegularSubgroup.map
        (MulAut.conj (productAutomorphism Φ).symm).toMonoidHom =
      rightRegularSubgroup) ∧
      derivativeGroupConjugateBy f Φ ∧
        ∀ x : A × B,
          Set.image (productAutomorphism Φ)
              (MathlibPlus.Open.ResearchFormalization.R1516Claim38054.normalizedDerivativeOrbit
                (conjugatedRowMap f Φ) x) =
            MathlibPlus.Open.ResearchFormalization.R1516Claim38054.normalizedDerivativeOrbit
              f ((productAutomorphism Φ) x)

end

end MathlibPlus.Open.ResearchFormalization.R1516Claim38053
