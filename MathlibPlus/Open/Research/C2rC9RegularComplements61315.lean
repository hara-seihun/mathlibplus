import Mathlib

namespace MathlibPlus.Open.Research.C2rC9RegularComplements61315

abbrev BinaryFactor (r : ℕ) := Fin r → ZMod 2
abbrev C2rC9 (r : ℕ) := BinaryFactor r × ZMod 9
abbrev C2rC9Mul (r : ℕ) := Multiplicative (C2rC9 r)

def c9RadicalAdd (r : ℕ) : AddSubgroup (C2rC9 r) :=
  AddSubgroup.prod (⊥ : AddSubgroup (BinaryFactor r))
    (⊤ : AddSubgroup (ZMod 9))

def c9TriadAdd (r : ℕ) : AddSubgroup (C2rC9 r) :=
  AddSubgroup.prod (⊥ : AddSubgroup (BinaryFactor r))
    (AddSubgroup.zmultiples (3 : ZMod 9))

def c9RadicalMul (r : ℕ) : Subgroup (C2rC9Mul r) :=
  AddSubgroup.toSubgroup (c9RadicalAdd r)

def c9TriadMul (r : ℕ) : Subgroup (C2rC9Mul r) :=
  AddSubgroup.toSubgroup (c9TriadAdd r)

def isNormalAddSubgroup {G : Type*} [AddGroup G]
    (H : AddSubgroup G) : Prop :=
  ∀ g : G, ∀ h : H, g + (h : G) - g ∈ H

def isThreeAddSubgroup {G : Type*} [AddGroup G]
    (H : AddSubgroup G) : Prop :=
  ∀ h : H, ∃ k : ℕ, addOrderOf (h : G) = 3 ^ k

def isOThreeAddSubgroup {G : Type*} [AddGroup G]
    (H : AddSubgroup G) : Prop :=
  isNormalAddSubgroup H ∧
    isThreeAddSubgroup H ∧
      ∀ K : AddSubgroup G,
        isNormalAddSubgroup K → isThreeAddSubgroup K → K ≤ H

def regularAdditiveAction {G Ω : Type*} [AddGroup G]
    (ρ : G → Equiv.Perm Ω) : Prop :=
  ρ 0 = 1 ∧
    (∀ g h : G, ρ (g + h) = ρ g * ρ h) ∧
      ∀ x y : Ω, ∃! g : G, ρ g x = y

def actionOrbit {G Ω : Type*}
    (ρ : G → Equiv.Perm Ω) (K : Set G) (x : Ω) : Set Ω :=
  {y | ∃ g : G, g ∈ K ∧ ρ g x = y}

def actionOrbitPartition {G Ω : Type*}
    (ρ : G → Equiv.Perm Ω) (K : Set G) : Set (Set Ω) :=
  {B | ∃ x : Ω, actionOrbit ρ K x = B}

def finiteSetPartition {Ω : Type*} (P : Set (Set Ω)) : Prop :=
  P.Nonempty ∧
    (∀ B : Set Ω, B ∈ P → B.Nonempty) ∧
      (∀ B C : Set Ω, B ∈ P → C ∈ P → B ≠ C → Disjoint B C) ∧
        ⋃₀ P = (Set.univ : Set Ω)

def invariantUnderAdditiveAction {G Ω : Type*}
    (ρ : G → Equiv.Perm Ω) (P : Set (Set Ω)) : Prop :=
  ∀ g : G, ∀ B : Set Ω, B ∈ P → ρ g '' B ∈ P

def invariantPartitionOfSize {G Ω : Type*}
    (ρ : G → Equiv.Perm Ω) (P : Set (Set Ω)) (n : ℕ) : Prop :=
  finiteSetPartition P ∧
    (∀ B : Set Ω, B ∈ P → B.ncard = n) ∧
      invariantUnderAdditiveAction ρ P

def regularC2rC9Copy {Ω : Type*} [Fintype Ω]
    (r : ℕ) (R : Subgroup (Equiv.Perm Ω)) : Prop :=
  (∀ x y : Ω, ∃! g : R, (g : Equiv.Perm Ω) x = y) ∧
    Nonempty (C2rC9Mul r ≃* R)

def generatedRegularPair {Ω : Type*}
    (R T : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))

def copiedSubgroup {G Ω : Type*} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃* R)
    (K : Subgroup G) : Subgroup (Equiv.Perm Ω) :=
  Subgroup.map (R.subtype.comp e.toMonoidHom) K

def characteristicSubgroupInCopy {Ω : Type*}
    (R K : Subgroup (Equiv.Perm Ω)) : Prop :=
  K ≤ R ∧
    ∀ φ : R ≃* R, ∀ k : R,
      ((k : Equiv.Perm Ω) ∈ K ↔ (φ k : Equiv.Perm Ω) ∈ K)

def permutationOrbit {Ω : Type*}
    (K : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ k : K, (k : Equiv.Perm Ω) x = y}

def permutationOrbitPartition {Ω : Type*}
    (K : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  {B | ∃ x : Ω, permutationOrbit K x = B}

def permutationPartitionInvariant {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (P : Set (Set Ω)) : Prop :=
  ∀ g : X, ∀ B : Set Ω, B ∈ P → (g : Equiv.Perm Ω) '' B ∈ P

def unorderedPairOrbital {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (e : Sym2 Ω) : Set (Sym2 Ω) :=
  Set.range (fun g : X => Sym2.map (g : Equiv.Perm Ω) e)

def unorderedPairOrbitalFamily {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) : Set (Set (Sym2 Ω)) :=
  {O | ∃ e : Sym2 Ω,
    (∃ x y : Ω, x ≠ y ∧ e = Sym2.mk x y) ∧
      O = unorderedPairOrbital X e}

def partitionPairRelation {Ω : Type*}
    (P : Set (Set Ω)) : Set (Sym2 Ω) :=
  {e | ∃ x y : Ω, x ≠ y ∧ Sym2.mk x y = e ∧
    ∃ B : Set Ω, B ∈ P ∧ x ∈ B ∧ y ∈ B}

def unionOfFullPairUnorderedOrbitals {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (P : Set (Set Ω)) : Prop :=
  ∃ F : Set (Set (Sym2 Ω)),
    F ⊆ unorderedPairOrbitalFamily X ∧
      partitionPairRelation P = ⋃₀ F

def characteristicFactorPartition {Ω : Type*}
    (r : ℕ) (R : Subgroup (Equiv.Perm Ω))
    (e : C2rC9Mul r ≃* R) (K : Subgroup (C2rC9Mul r)) : Set (Set Ω) :=
  permutationOrbitPartition (copiedSubgroup R e K)

def regularPairCharacteristicAlignment {Ω : Type*} [Fintype Ω]
    (r : ℕ) (R T : Subgroup (Equiv.Perm Ω))
    (eR : C2rC9Mul r ≃* R) (eT : C2rC9Mul r ≃* T) : Prop :=
  let X := generatedRegularPair R T
  let TR := characteristicFactorPartition r R eR (c9TriadMul r)
  let TT := characteristicFactorPartition r T eT (c9TriadMul r)
  let CR := characteristicFactorPartition r R eR (c9RadicalMul r)
  let CT := characteristicFactorPartition r T eT (c9RadicalMul r)
  characteristicSubgroupInCopy R (copiedSubgroup R eR (c9TriadMul r)) ∧
    characteristicSubgroupInCopy T (copiedSubgroup T eT (c9TriadMul r)) ∧
    characteristicSubgroupInCopy R (copiedSubgroup R eR (c9RadicalMul r)) ∧
    characteristicSubgroupInCopy T (copiedSubgroup T eT (c9RadicalMul r)) ∧
    ((permutationPartitionInvariant X TR ∨
        permutationPartitionInvariant X TT) → TR = TT) ∧
    ((permutationPartitionInvariant X CR ∨
        permutationPartitionInvariant X CT) → CR = CT) ∧
    (TR ≠ TT →
      ¬ (unionOfFullPairUnorderedOrbitals X TR ∨
        unionOfFullPairUnorderedOrbitals X TT))

def claim61315 : Prop :=
  (∀ (r : ℕ) (Ω : Type*) [Fintype Ω]
      (ρ : C2rC9 r → Equiv.Perm Ω),
      regularAdditiveAction ρ →
        let U := c9RadicalAdd r
        let U3 := c9TriadAdd r
        isOThreeAddSubgroup U ∧
          Nonempty (U ≃+ ZMod 9) ∧
          (∀ P : Set (Set Ω),
            invariantPartitionOfSize ρ P 3 →
              P = actionOrbitPartition ρ (U3 : Set (C2rC9 r))) ∧
          (∀ P : Set (Set Ω),
            invariantPartitionOfSize ρ P 9 →
              P = actionOrbitPartition ρ (U : Set (C2rC9 r)))) ∧
    (∀ (r : ℕ) (Ω : Type*) [Fintype Ω]
      (R T : Subgroup (Equiv.Perm Ω)),
      regularC2rC9Copy r R →
        regularC2rC9Copy r T →
          ∀ eR : C2rC9Mul r ≃* R,
            ∀ eT : C2rC9Mul r ≃* T,
              regularPairCharacteristicAlignment r R T eR eT)

end MathlibPlus.Open.Research.C2rC9RegularComplements61315
