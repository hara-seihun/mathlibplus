import Mathlib

namespace MathlibPlus.Open.Frontier.CICoprimeShellProductsC6BlockLiftObstruction

abbrev Omega := Fin 6
abbrev G := Equiv.Perm Omega

def t : G :=
  { toFun := ![(1 : Omega), 2, 0, 4, 5, 3]
    invFun := ![(2 : Omega), 0, 1, 5, 3, 4]
    left_inv := by decide
    right_inv := by decide }

def s : G :=
  { toFun := ![(3 : Omega), 4, 5, 0, 1, 2]
    invFun := ![(3 : Omega), 4, 5, 0, 1, 2]
    left_inv := by decide
    right_inv := by decide }

def f : G :=
  { toFun := ![(0 : Omega), 1, 2, 3, 5, 4]
    invFun := ![(0 : Omega), 1, 2, 3, 5, 4]
    left_inv := by decide
    right_inv := by decide }

def conjugateSubgroup (u : G) (H : Subgroup G) : Subgroup G where
  carrier := {x | u⁻¹ * x * u ∈ H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change u⁻¹ * a * u ∈ H at ha
    change u⁻¹ * b * u ∈ H at hb
    change u⁻¹ * (a * b) * u ∈ H
    simpa [mul_assoc] using H.mul_mem ha hb
  inv_mem' := by
    intro a ha
    change u⁻¹ * a * u ∈ H at ha
    change u⁻¹ * a⁻¹ * u ∈ H
    simpa [mul_assoc] using H.inv_mem ha

def L : Subgroup G := Subgroup.closure ({t, s} : Set G)
def R : Subgroup G := conjugateSubgroup f L
def A : Subgroup G := Subgroup.closure ((L : Set G) ∪ (R : Set G))

def L3 : Subgroup G := Subgroup.closure ({t} : Set G)
def R3 : Subgroup G := conjugateSubgroup f L3

def block₀ : Set Omega := {0, 1, 2}
def block₁ : Set Omega := {3, 4, 5}
def blocks : Set (Set Omega) := {block₀, block₁}

def orbit (H : Subgroup G) (x : Omega) : Set Omega :=
  {y | ∃ h : H, (h : G) x = y}

def orbitPartition (H : Subgroup G) : Set (Set Omega) :=
  {B | ∃ x : Omega, orbit H x = B}

def IsRegularCopyOfC6 (H : Subgroup G) : Prop :=
  (∀ x y : Omega, ∃! h : H, (h : G) x = y) ∧
    Nonempty (H ≃* Multiplicative (ZMod 6))

def IsCharacteristicOrderThree (K H : Subgroup G) : Prop :=
  K ≤ H ∧
    Nat.card K = 3 ∧
      ∀ e : H ≃* H, ∀ x : H,
        ((x : G) ∈ K ↔ ((e x : H) : G) ∈ K)

def CorrespondingElementsAgreeOnBlocks : Prop :=
  ∀ x : L, ∀ B : Set Omega, B ∈ blocks →
    Set.image ((x : G) : Omega → Omega) B =
      Set.image ((f * (x : G) * f⁻¹ : G) : Omega → Omega) B

def claim_59788 : Prop :=
  L ≠ R ∧
    IsRegularCopyOfC6 L ∧
      IsRegularCopyOfC6 R ∧
        IsCharacteristicOrderThree L3 L ∧
          IsCharacteristicOrderThree R3 R ∧
            orbitPartition L3 = blocks ∧
              orbitPartition R3 = blocks ∧
                CorrespondingElementsAgreeOnBlocks ∧
                  ∀ g : A, conjugateSubgroup (g : G) L ≠ R

end MathlibPlus.Open.Frontier.CICoprimeShellProductsC6BlockLiftObstruction
