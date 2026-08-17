import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2888Claim47374

noncomputable section

/-- A specified group copy acts regularly on the finite permutation domain. -/
def regularPermutationCopy {X Ω : Type*} [Group X]
    (R : Subgroup (Equiv.Perm Ω)) (e : X ≃* R) : Prop :=
  ∀ x y : Ω, ∃! h : X, ((e h : R) : Equiv.Perm Ω) x = y

/-- A subgroup of a group is invariant under every automorphism of its parent. -/
def characteristicSubgroup {E : Type*} [Group E]
    (R P : Subgroup E) : Prop :=
  P ≤ R ∧
    ∀ φ : R ≃* R, ∀ r : R,
      (r : E) ∈ P ↔ (φ r : E) ∈ P

/-- The Hall subgroup for the primes in the displayed finite order. -/
def hallPi {E : Type*} [Group E]
    (R P : Subgroup E) (n : ℕ) : Prop :=
  P ≤ R ∧
    (∀ p : ℕ, Nat.Prime p →
      (p ∣ Nat.card P ↔ p ∣ Nat.card R ∧ p ∣ n)) ∧
    Nat.Coprime (Nat.card P) (Nat.card R / Nat.card P)

/-- A characteristic Hall subgroup for the primes of `n`. -/
def characteristicHallPi {E : Type*} [Group E]
    (R P : Subgroup E) (n : ℕ) : Prop :=
  characteristicSubgroup R P ∧ hallPi R P n

/-- The orbit of a point under a permutation subgroup. -/
def subgroupOrbit {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ p : P, (p : Equiv.Perm Ω) x = y}

/-- The actual orbit partition of a permutation subgroup. -/
def subgroupOrbitPartition {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  Set.range (subgroupOrbit P)

/-- A permutation maps every named block to a named block. -/
def setwiseStabilizerOfPartition {Ω : Type*}
    (f : Equiv.Perm Ω) (B : Set (Set Ω)) : Prop :=
  ∀ C : Set Ω, C ∈ B ↔ f '' C ∈ B

/-- The induced permutation of a genuine block quotient, expressed by its action
on every actual block rather than by an unconstrained callback. -/
def inducesBlockPermutation {Ω : Type*}
    (B : Set (Set Ω)) (f : Equiv.Perm Ω) (q : Equiv.Perm B) : Prop :=
  ∀ C : B, ((q C : B) : Set Ω) = f '' (C : Set Ω)

/-- The exact image of a permutation subgroup on the named block system. -/
def actualBlockImage {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω))
    (L : Subgroup (Equiv.Perm B)) : Prop :=
  (∀ m : M, ∃! q : Equiv.Perm B,
    inducesBlockPermutation B (m : Equiv.Perm Ω) q) ∧
    (∀ q : Equiv.Perm B, q ∈ L ↔
      ∃ m : M, inducesBlockPermutation B (m : Equiv.Perm Ω) q)

/-- Conjugation in the convention `S^f = f⁻¹ S f`. -/
def conjugateSubgroupBy {E : Type*} [Group E]
    (f : E) (S : Subgroup E) : Subgroup E :=
  Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj f⁻¹)) S

/-- Conjugation maps one specified subgroup onto another. -/
def mapsSubgroupBy {E : Type*} [Group E]
    (f : E) (S T : Subgroup E) : Prop :=
  conjugateSubgroupBy f S = T

/-- The induced quotient copy is transported by the induced block permutation. -/
def mapsInducedBlockCopy {Ω : Type*}
    (f : Equiv.Perm Ω) (B : Set (Set Ω))
    (LR LT : Subgroup (Equiv.Perm B)) : Prop :=
  ∃ q : Equiv.Perm B,
    inducesBlockPermutation B f q ∧ conjugateSubgroupBy q LR = LT

/-- An element of the actual kernel of the block action. -/
def blockKernelElement {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω)) :=
  {m : M // ∀ C : B, (m : Equiv.Perm Ω) '' (C : Set Ω) = (C : Set Ω)}

/-- Claim 47374: after the specified setwise block and quotient alignment,
the common Hall subgroup is literal equality and the remaining conjugator lies
in the actual block-action kernel. -/
def claim47374 : Prop :=
  ∀ (A H Ω : Type*) [CommGroup A] [Group H]
    [Fintype A] [Fintype H] [Fintype Ω]
    (G R T P Q : Subgroup (Equiv.Perm Ω))
    (B : Set (Set Ω))
    (LR LT : Subgroup (Equiv.Perm B))
    (eR : A × H ≃* R) (eT : A × H ≃* T),
    Nat.Coprime (Nat.card A) (Nat.card H) →
    R ≤ G → T ≤ G →
    regularPermutationCopy R eR →
    regularPermutationCopy T eT →
    characteristicHallPi R P (Nat.card A) →
    characteristicHallPi T Q (Nat.card A) →
    subgroupOrbitPartition P = B →
    subgroupOrbitPartition Q = B →
    (∃ f : Equiv.Perm Ω,
      setwiseStabilizerOfPartition f B ∧
      mapsSubgroupBy f P Q ∧
      actualBlockImage R B LR ∧
      actualBlockImage T B LT ∧
      mapsInducedBlockCopy f B LR LT) →
    ∃ f : Equiv.Perm Ω,
      setwiseStabilizerOfPartition f B ∧
      mapsSubgroupBy f P Q ∧
      mapsInducedBlockCopy f B LR LT ∧
      let R' := conjugateSubgroupBy f R
      let P' := conjugateSubgroupBy f P
      let M' := Subgroup.closure
        ((R' : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))
      P' = Q ∧
        actualBlockImage R' B LT ∧
        actualBlockImage T B LT ∧
        ∃ k : blockKernelElement M' B,
          conjugateSubgroupBy ((k.1 : M') : Equiv.Perm Ω) R' = T

end
end MathlibPlus.Open.ResearchFormalization.R2888Claim47374
