import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5018.Claim55029

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

abbrev Coker (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Module ℚ X] [Module ℚ Y] (f : Hom X Y) := Y ⧸ LinearMap.range f

def lambdaMap
    (P : Submodule ℚ (Hom C0 C1)) (L1 : Hom C1 W1) :
    P →ₗ[ℚ] Hom C0 W1 :=
  (LinearMap.compRight ℚ L1).comp P.subtype

def scalarTarget (L0 : Hom C0 W0) (S : Hom W0 W1) : Hom C0 W1 :=
  S.comp L0

def scalarCokernelClass
    (P : Submodule ℚ (Hom C0 C1)) (L0 : Hom C0 W0)
    (L1 : Hom C1 W1) (S : Hom W0 W1) :
    Coker P (Hom C0 W1) (lambdaMap P L1) :=
  (LinearMap.range (lambdaMap P L1)).mkQ (scalarTarget L0 S)

def claim55029
    (P : Submodule ℚ (Hom C0 C1))
    (L0 : Hom C0 W0) (L1 : Hom C1 W1)
    (S : Hom W0 W1) : Prop :=
  let Λ := lambdaMap P L1
  let t_S := scalarTarget L0 S
  let obstruction := (LinearMap.range Λ).mkQ t_S
  (obstruction = 0 ↔
      ∃ E : P, L1.comp E.1 = S.comp L0) ∧
    (obstruction ≠ 0 →
      ∃ μ : Module.Dual ℚ (Hom C0 W1),
        (∀ E : P, μ (Λ E) = 0) ∧ μ t_S ≠ 0)

end MathlibPlus.Open.ResearchFormalization.R5018.Claim55029
