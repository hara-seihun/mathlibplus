import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5018.Claim55032

universe uC0 uC1 uW0 uW1 uZ

variable {C0 : Type uC0} {C1 : Type uC1}
  {W0 : Type uW0} {W1 : Type uW1} {Z : Type uZ}
variable [AddCommGroup C0] [AddCommGroup C1]
  [AddCommGroup W0] [AddCommGroup W1] [AddCommGroup Z]
variable [Module ℚ C0] [Module ℚ C1]
  [Module ℚ W0] [Module ℚ W1] [Module ℚ Z]
variable [FiniteDimensional ℚ C0] [FiniteDimensional ℚ C1]
  [FiniteDimensional ℚ W0] [FiniteDimensional ℚ W1]
  [FiniteDimensional ℚ Z]

abbrev Hom (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Module ℚ X] [Module ℚ Y] := X →ₗ[ℚ] Y

def scalarNullSpace
    (P : Submodule ℚ (Hom C0 C1)) (L1 : Hom C1 W1) :
    Submodule ℚ (Hom C0 C1) :=
  P ⊓ LinearMap.ker (LinearMap.compRight ℚ L1)

def responseMap
    (P : Submodule ℚ (Hom C0 C1)) (L1 : Hom C1 W1)
    (A1 : Hom C1 Z) :
    scalarNullSpace P L1 →ₗ[ℚ] Hom C0 Z :=
  (LinearMap.compRight ℚ A1).comp (scalarNullSpace P L1).subtype

def scalarCoboundaryMap
    (L0 : Hom C0 W0) :
    Hom W0 Z →ₗ[ℚ] Hom C0 Z :=
  LinearMap.lcomp ℚ Z L0

def responseStageOneClass
    (L0 : Hom C0 W0) (A0 : Hom C0 Z) (A1 : Hom C1 Z)
    (E : Hom C0 C1) :
      (Hom C0 Z) ⧸ LinearMap.range (scalarCoboundaryMap L0) :=
  (LinearMap.range (scalarCoboundaryMap L0)).mkQ (A1.comp E - A0)

def responseDeformationMap
    (P : Submodule ℚ (Hom C0 C1)) (L0 : Hom C0 W0)
    (L1 : Hom C1 W1) (A1 : Hom C1 Z) :
    scalarNullSpace P L1 →ₗ[ℚ]
      (Hom C0 Z) ⧸ LinearMap.range (scalarCoboundaryMap L0) :=
  (LinearMap.range (scalarCoboundaryMap L0)).mkQ.comp
    (responseMap P L1 A1)

def allLiftsResponseClass
    (P : Submodule ℚ (Hom C0 C1)) (L0 : Hom C0 W0)
    (L1 : Hom C1 W1) (A0 : Hom C0 Z) (A1 : Hom C1 Z)
    (E : Hom C0 C1) :
      ((Hom C0 Z) ⧸ LinearMap.range (scalarCoboundaryMap L0)) ⧸
        LinearMap.range (responseDeformationMap P L0 L1 A1) :=
  (LinearMap.range (responseDeformationMap P L0 L1 A1)).mkQ
    (responseStageOneClass L0 A0 A1 E)

def claim55032
    (P : Submodule ℚ (Hom C0 C1))
    (L0 : Hom C0 W0) (L1 : Hom C1 W1)
    (S : Hom W0 W1)
    (A0 : Hom C0 Z) (A1 : Hom C1 Z) : Prop :=
  ∀ E0 : P, L1.comp E0.1 = S.comp L0 →
    allLiftsResponseClass P L0 L1 A0 A1 E0.1 ≠ 0 →
    ∃ μ : Module.Dual ℚ (Hom C0 Z),
      (∀ Ψ : Hom W0 Z, μ (Ψ.comp L0) = 0) ∧
      (∀ K : scalarNullSpace P L1, μ (A1.comp K.1) = 0) ∧
      μ (A1.comp E0.1 - A0) ≠ 0 ∧
      (∀ E : P, L1.comp E.1 = S.comp L0 →
        μ (A1.comp E.1 - A0) ≠ 0)

end MathlibPlus.Open.ResearchFormalization.R5018.Claim55032
