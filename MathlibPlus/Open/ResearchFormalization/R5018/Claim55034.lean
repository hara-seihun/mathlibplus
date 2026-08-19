import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5018.Claim55034

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

def lambdaMap
    (P : Submodule ℚ (Hom C0 C1)) (L1 : Hom C1 W1) :
    P →ₗ[ℚ] Hom C0 W1 :=
  (LinearMap.compRight ℚ L1).comp P.subtype

def scalarCokernelClass
    (P : Submodule ℚ (Hom C0 C1)) (L0 : Hom C0 W0)
    (L1 : Hom C1 W1) (S : Hom W0 W1) :
    (Hom C0 W1) ⧸ LinearMap.range (lambdaMap P L1) :=
  (LinearMap.range (lambdaMap P L1)).mkQ (S.comp L0)

def scalarNullSpace
    (P : Submodule ℚ (Hom C0 C1)) (L1 : Hom C1 W1) :
    Submodule ℚ (Hom C0 C1) :=
  P ⊓ LinearMap.ker (LinearMap.compRight ℚ L1)

def responseMap
    (P : Submodule ℚ (Hom C0 C1)) (A1 : Hom C1 Z) :
    P →ₗ[ℚ] Hom C0 Z :=
  (LinearMap.compRight ℚ A1).comp P.subtype

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
    ((LinearMap.compRight ℚ A1).comp (scalarNullSpace P L1).subtype)

def allLiftsResponseClass
    (P : Submodule ℚ (Hom C0 C1)) (L0 : Hom C0 W0)
    (L1 : Hom C1 W1) (A0 : Hom C0 Z) (A1 : Hom C1 Z)
    (E : Hom C0 C1) :
      ((Hom C0 Z) ⧸ LinearMap.range (scalarCoboundaryMap L0)) ⧸
        LinearMap.range (responseDeformationMap P L0 L1 A1) :=
  (LinearMap.range (responseDeformationMap P L0 L1 A1)).mkQ
    (responseStageOneClass L0 A0 A1 E)

def jointMap
    (P : Submodule ℚ (Hom C0 C1))
    (L0 : Hom C0 W0) (L1 : Hom C1 W1)
    (A1 : Hom C1 Z) :
    (P × Hom W0 Z) →ₗ[ℚ] (Hom C0 W1 × Hom C0 Z) :=
  LinearMap.prod
    ((lambdaMap P L1).comp (LinearMap.fst ℚ P (Hom W0 Z)))
    (((responseMap P A1).comp (LinearMap.fst ℚ P (Hom W0 Z))) -
      (scalarCoboundaryMap L0).comp (LinearMap.snd ℚ P (Hom W0 Z)))

def jointTarget
    (L0 : Hom C0 W0) (S : Hom W0 W1) (A0 : Hom C0 Z) :
    Hom C0 W1 × Hom C0 Z :=
  (S.comp L0, A0)

def jointCokernelClass
    (P : Submodule ℚ (Hom C0 C1))
    (L0 : Hom C0 W0) (L1 : Hom C1 W1)
    (S : Hom W0 W1) (A0 : Hom C0 Z) (A1 : Hom C1 Z) :
    (Hom C0 W1 × Hom C0 Z) ⧸
      LinearMap.range (jointMap P L0 L1 A1) :=
  (LinearMap.range (jointMap P L0 L1 A1)).mkQ
    (jointTarget L0 S A0)

def claim55034
    (P : Submodule ℚ (Hom C0 C1))
    (L0 : Hom C0 W0) (L1 : Hom C1 W1)
    (S : Hom W0 W1)
    (A0 : Hom C0 Z) (A1 : Hom C1 Z) : Prop :=
  let T := jointMap P L0 L1 A1
  let b_S := jointTarget L0 S A0
  let jointClass := (LinearMap.range T).mkQ b_S
  (jointClass = 0 ↔
      ∃ E : P, ∃ Ψ : Hom W0 Z,
        L1.comp E.1 = S.comp L0 ∧
        A1.comp E.1 = A0 + Ψ.comp L0) ∧
    (jointClass = 0 ↔
      scalarCokernelClass P L0 L1 S = 0 ∧
      ∃ E0 : P,
        L1.comp E0.1 = S.comp L0 ∧
        allLiftsResponseClass P L0 L1 A0 A1 E0.1 = 0) ∧
    (jointClass ≠ 0 →
      ∃ ν : Module.Dual ℚ (Hom C0 W1 × Hom C0 Z),
        (∀ x : P × Hom W0 Z, ν (T x) = 0) ∧ ν b_S ≠ 0)

end MathlibPlus.Open.ResearchFormalization.R5018.Claim55034
