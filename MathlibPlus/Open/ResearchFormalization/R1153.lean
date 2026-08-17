import Mathlib
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups
import MathlibPlus.Open.GraphTheory.IntersectionSignaturesBatch
import MathlibPlus.Open.ResearchFormalization.MinimumBlockAction

namespace MathlibPlus.Open.ResearchFormalization.R1153

abbrev Q8 := QuaternionGroup 2
abbrev BlockType {Ω : Type*} (B : Finset (Set Ω)) :=
  MathlibPlus.Open.blockType B


def commonNontrivialBlockSystem {Ω : Type*} (B : Finset (Set Ω)) : Prop :=
  MathlibPlus.Open.finiteBlockSystem B ∧
    (B : Set (Set Ω)) ≠ {Set.univ} ∧
    ¬ MathlibPlus.Open.ResearchFormalization.singletonBlockSystem
      (B : Set (Set Ω))


def kernelIntersection31617
    {Ω : Type*} {B : Finset (Set Ω)}
    {X : Subgroup (Equiv.Perm Ω)}
    (π : X →* Equiv.Perm (BlockType B))
    (S : Subgroup X) : Subgroup S :=
  Subgroup.comap S.subtype π.ker


def blockStabilizerMembership31617
    {Ω : Type*} {B : Finset (Set Ω)}
    {X : Subgroup (Equiv.Perm Ω)}
    (S : Subgroup X) (U : BlockType B) (s : S) : Prop :=
  (((s.1 : X) : Equiv.Perm Ω) '' U.1 = U.1)


def regularOnEveryBlock31617
    {Ω : Type*} {B : Finset (Set Ω)}
    {X : Subgroup (Equiv.Perm Ω)}
    (π : X →* Equiv.Perm (BlockType B))
    (S : Subgroup X) : Prop :=
  ∀ U : BlockType B,
    (∀ k : kernelIntersection31617 π S, ∀ x : Ω, x ∈ U.1 →
      ((k.1.1 : X) : Equiv.Perm Ω) x ∈ U.1) ∧
    (∀ x y : Ω, x ∈ U.1 → y ∈ U.1 →
      ∃! k : kernelIntersection31617 π S,
        ((k.1.1 : X) : Equiv.Perm Ω) x = y)


def claim31617 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Equiv.Perm Ω))
      (R T : Subgroup X)
      (B : Finset (Set Ω))
      (π : X →* Equiv.Perm (BlockType B)),
      Nonempty (R ≃* (A × Q8)) →
      Nonempty (T ≃* (A × Q8)) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (R.map X.subtype) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (T.map X.subtype) →
      Subgroup.closure ((R : Set X) ∪ (T : Set X)) = ⊤ →
      commonNontrivialBlockSystem B →
      (∀ (x : X) (U : BlockType B),
        ((π x) U).1 = ((x : Equiv.Perm Ω) '' U.1)) →
      (∀ U : BlockType B, ∀ s : R,
        blockStabilizerMembership31617 R U s ↔ s.1 ∈ π.ker) ∧
      (∀ U : BlockType B, ∀ s : T,
        blockStabilizerMembership31617 T U s ↔ s.1 ∈ π.ker) ∧
      regularOnEveryBlock31617 π R ∧
      regularOnEveryBlock31617 π T ∧
      (∀ S : Subgroup X, S = R ∨ S = T →
        MathlibPlus.Open.regularSubgroupOnBlocks (S.map π))


def oneOfFour31618 (p₁ p₂ p₃ p₄ : Prop) : Prop :=
  (p₁ ∧ ¬ p₂ ∧ ¬ p₃ ∧ ¬ p₄) ∨
    (¬ p₁ ∧ p₂ ∧ ¬ p₃ ∧ ¬ p₄) ∨
    (¬ p₁ ∧ ¬ p₂ ∧ p₃ ∧ ¬ p₄) ∨
    (¬ p₁ ∧ ¬ p₂ ∧ ¬ p₃ ∧ p₄)


def blockSubgroupQuotientTaxonomy31618
    {A : Type*} [CommGroup A]
    (H Q : Type*) [Group H] [Group Q]
    (C : Subgroup A) : Prop :=
  oneOfFour31618
    (Nonempty (H ≃* C) ∧
      Nonempty (Q ≃* ((A ⧸ C) × Q8)))
    (Nonempty (H ≃* (C × ZMod 2)) ∧
      Nonempty (Q ≃* ((A ⧸ C) × (ZMod 2 × ZMod 2))))
    (Nonempty (H ≃* (C × ZMod 4)) ∧
      Nonempty (Q ≃* ((A ⧸ C) × ZMod 2)))
    (Nonempty (H ≃* (C × Q8)) ∧
      Nonempty (Q ≃* (A ⧸ C)))


def blockSubgroupQuotientTaxonomyExact31618
    {A : Type*} [CommGroup A]
    (H Q : Type*) [Group H] [Group Q] : Prop :=
  ∃ C : Subgroup A,
    blockSubgroupQuotientTaxonomy31618 H Q C ∧
      ¬ Nonempty (H ≃* (ZMod 2 × ZMod 2))


def claim31618 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Equiv.Perm Ω))
      (R T : Subgroup X)
      (B : Finset (Set Ω))
      (π : X →* Equiv.Perm (BlockType B)),
      Nonempty (R ≃* (A × Q8)) →
      Nonempty (T ≃* (A × Q8)) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (R.map X.subtype) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (T.map X.subtype) →
      Subgroup.closure ((R : Set X) ∪ (T : Set X)) = ⊤ →
      commonNontrivialBlockSystem B →
      (∀ (x : X) (U : BlockType B),
        ((π x) U).1 = ((x : Equiv.Perm Ω) '' U.1)) →
      (∀ S : Subgroup X, S = R ∨ S = T →
        MathlibPlus.Open.regularSubgroupOnBlocks (S.map π) →
        blockSubgroupQuotientTaxonomyExact31618 (A := A)
          (↥(kernelIntersection31617 π S)) (↥(S.map π)))


def localKernelImage31619
    {Ω : Type*} {B : Finset (Set Ω)}
    {X : Subgroup (Equiv.Perm Ω)}
    (π : X →* Equiv.Perm (BlockType B))
    (U : BlockType B) : Set (Equiv.Perm U.1) :=
  {h | ∃ k : π.ker, ∃ hk :
      ((k.1 : X) : Equiv.Perm Ω) '' U.1 = U.1,
      h = MathlibPlus.Open.ResearchFormalization.restrictPermutation
        ((k.1 : X) : Equiv.Perm Ω) U.1 hk}


def localIntersectionImage31619
    {Ω : Type*} {B : Finset (Set Ω)}
    {X : Subgroup (Equiv.Perm Ω)}
    (π : X →* Equiv.Perm (BlockType B))
    (S : Subgroup X) (U : BlockType B) : Set (Equiv.Perm U.1) :=
  {h | ∃ k : kernelIntersection31617 π S, ∃ hk :
      ((k.1.1 : X) : Equiv.Perm Ω) '' U.1 = U.1,
      h = MathlibPlus.Open.ResearchFormalization.restrictPermutation
        ((k.1.1 : X) : Equiv.Perm Ω) U.1 hk}


def regularPermutationSet31619 {α : Type*}
    (L : Set (Equiv.Perm α)) : Prop :=
  ∀ x y : α, ∃! h, h ∈ L ∧ h x = y


def localKernelImageNormalTransitive31619 {α : Type*}
    (H L C : Set (Equiv.Perm α)) : Prop :=
  (1 : Equiv.Perm α) ∈ L ∧
    (∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) ∧
    (∀ a ∈ L, a⁻¹ ∈ L) ∧
    regularPermutationSet31619 C ∧
    C ⊆ L ∧
    (∀ x y : α, ∃ h ∈ L, h x = y) ∧
    (∀ l ∈ L, ∀ h ∈ H, h * l * h⁻¹ ∈ L)


def claim31619 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Equiv.Perm Ω))
      (R T : Subgroup X)
      (B : Finset (Set Ω))
      (π : X →* Equiv.Perm (BlockType B)),
      Nonempty (R ≃* (A × Q8)) →
      Nonempty (T ≃* (A × Q8)) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (R.map X.subtype) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (T.map X.subtype) →
      Subgroup.closure ((R : Set X) ∪ (T : Set X)) = ⊤ →
      commonNontrivialBlockSystem B →
      (∀ (x : X) (U : BlockType B),
        ((π x) U).1 = ((x : Equiv.Perm Ω) '' U.1)) →
      MathlibPlus.Open.ResearchFormalization.minimumNontrivialBlockSystem
          (X : Set (Equiv.Perm Ω)) (B : Set (Set Ω)) →
      (∀ U : BlockType B,
        MathlibPlus.Open.ResearchFormalization.primitivePermutationSet
          (MathlibPlus.Open.ResearchFormalization.inducedLocalPermutations
            (X : Set (Equiv.Perm Ω)) U.1)) ∧
      (∀ U : BlockType B,
        localKernelImageNormalTransitive31619
          (MathlibPlus.Open.ResearchFormalization.inducedLocalPermutations
            (X : Set (Equiv.Perm Ω)) U.1)
          (localKernelImage31619 π U)
          (localIntersectionImage31619 π R U))


def mixedEvenBlockType31620
    {A : Type*} [CommGroup A]
    (H : Type*) [Group H] : Prop :=
  (∃ C : Subgroup A, C = ⊥ ∧ Nonempty (H ≃* ZMod 2)) ∨
    (∃ C : Subgroup A, C ≠ ⊥ ∧
      (Nonempty (H ≃* (C × ZMod 2)) ∨
        Nonempty (H ≃* (C × ZMod 4)) ∨
        Nonempty (H ≃* (C × Q8))))


def centralInvolution31620
    {Ω : Type*} {X : Subgroup (Equiv.Perm Ω)}
    (S : Subgroup X) (z : Equiv.Perm Ω) : Prop :=
  z ∈ (S.map X.subtype : Set (Equiv.Perm Ω)) ∧
    z ≠ 1 ∧ z * z = 1 ∧
    ∀ s : S,
      z * ((s.1 : X) : Equiv.Perm Ω) =
        ((s.1 : X) : Equiv.Perm Ω) * z


def conjugatedSecondCentralInvolution31620
    {Ω : Type*} {X : Subgroup (Equiv.Perm Ω)}
    (T : Subgroup X) (δ : X) (z : Equiv.Perm Ω) : Prop :=
  (∃ t : T,
    z = ((δ : Equiv.Perm Ω)⁻¹ *
      ((t.1 : X) : Equiv.Perm Ω) * (δ : Equiv.Perm Ω))) ∧
    (∀ t : T,
      z * ((δ : Equiv.Perm Ω)⁻¹ *
        ((t.1 : X) : Equiv.Perm Ω) * (δ : Equiv.Perm Ω)) =
        ((δ : Equiv.Perm Ω)⁻¹ *
          ((t.1 : X) : Equiv.Perm Ω) * (δ : Equiv.Perm Ω)) * z)


def involutionOrbitSystem31620
    {Ω : Type*} (z : Equiv.Perm Ω) : Set (Set Ω) :=
  Set.range (fun x : Ω => ({x, z x} : Set Ω))


def normalTwoPointOrbitSystem31620
    {Ω : Type*} (X : Subgroup (Equiv.Perm Ω))
    (z : Equiv.Perm Ω) : Prop :=
  MathlibPlus.Open.ResearchFormalization.permutationSetBlockSystem
      (X : Set (Equiv.Perm Ω)) (involutionOrbitSystem31620 z) ∧
    (∀ C ∈ involutionOrbitSystem31620 z, C.ncard = 2)


def claim31620 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Equiv.Perm Ω))
      (R T : Subgroup X)
      (B : Finset (Set Ω))
      (π : X →* Equiv.Perm (BlockType B)),
      Nonempty (R ≃* (A × Q8)) →
      Nonempty (T ≃* (A × Q8)) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (R.map X.subtype) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (T.map X.subtype) →
      Subgroup.closure ((R : Set X) ∪ (T : Set X)) = ⊤ →
      commonNontrivialBlockSystem B →
      (∀ (x : X) (U : BlockType B),
        ((π x) U).1 = ((x : Equiv.Perm Ω) '' U.1)) →
      MathlibPlus.Open.ResearchFormalization.minimumNontrivialBlockSystem
          (X : Set (Equiv.Perm Ω)) (B : Set (Set Ω)) →
      (∀ U : BlockType B,
        mixedEvenBlockType31620 (A := A)
          (↥(kernelIntersection31617 π R)) →
          ∃ δ : π.ker, ∃ z : Equiv.Perm Ω,
            centralInvolution31620 R z ∧
            conjugatedSecondCentralInvolution31620 T (δ.1 : X) z ∧
            normalTwoPointOrbitSystem31620 X z)

end MathlibPlus.Open.ResearchFormalization.R1153
