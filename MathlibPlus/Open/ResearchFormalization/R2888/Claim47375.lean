import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2888Claim47375

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

/-- The Hall subgroup for the complementary primes in the parent order. -/
def hallPiPrime {E : Type*} [Group E]
    (R U : Subgroup E) (n : ℕ) : Prop :=
  U ≤ R ∧
    (∀ p : ℕ, Nat.Prime p →
      (p ∣ Nat.card U ↔ p ∣ Nat.card R ∧ ¬p ∣ n)) ∧
    Nat.Coprime (Nat.card U) (Nat.card R / Nat.card U)

/-- A characteristic Hall subgroup for the primes of `n`. -/
def characteristicHallPi {E : Type*} [Group E]
    (R P : Subgroup E) (n : ℕ) : Prop :=
  characteristicSubgroup R P ∧ hallPi R P n

/-- A characteristic Hall subgroup for the complementary primes of `n`. -/
def characteristicHallPiPrime {E : Type*} [Group E]
    (R U : Subgroup E) (n : ℕ) : Prop :=
  characteristicSubgroup R U ∧ hallPiPrime R U n

/-- The orbit of a point under a permutation subgroup. -/
def subgroupOrbit {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (x : Ω) : Set Ω :=
  {y | ∃ p : P, (p : Equiv.Perm Ω) x = y}

/-- The actual orbit partition of a permutation subgroup. -/
def subgroupOrbitPartition {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) : Set (Set Ω) :=
  Set.range (subgroupOrbit P)

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

/-- An element of the actual kernel of the block action. -/
def blockKernelElement {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω)) :=
  {m : M // ∀ C : B, (m : Equiv.Perm Ω) '' (C : Set Ω) = (C : Set Ω)}

/-- The aligned finite-abelian Hall setup, with `L` the actual common block image. -/
def alignedHallSetup
    (A H Ω : Type*) [CommGroup A] [Group H]
    [Fintype A] [Fintype H] [Fintype Ω]
    (R T P : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω))
    (L : Subgroup (Equiv.Perm B))
    (eR : A × H ≃* R) (eT : A × H ≃* T) : Prop :=
  regularPermutationCopy R eR ∧
    regularPermutationCopy T eT ∧
    characteristicHallPi R P (Nat.card A) ∧
    characteristicHallPi T P (Nat.card A) ∧
    subgroupOrbitPartition P = B ∧
    actualBlockImage R B L ∧
    actualBlockImage T B L ∧
    actualBlockImage
      (Subgroup.closure ((R : Set (Equiv.Perm Ω)) ∪
        (T : Set (Equiv.Perm Ω)))) B L

/-- Both regular copies centralize the common Hall subgroup. -/
def centralizesSubgroup {E : Type*} [Group E]
    (P R : Subgroup E) : Prop :=
  ∀ p : P, ∀ r : R, (p : E) * (r : E) = (r : E) * (p : E)

/-- On each block, the centralizer of the regular abelian Hall action is its
opposite regular action. -/
def blockCentralizerEqualsHall {Ω : Type*}
    (P : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω)) : Prop :=
  ∀ C : Set Ω, C ∈ B →
    ∀ f : Equiv.Perm Ω,
      ((f '' C = C) ∧
        (∀ p : P, ∀ x : Ω, x ∈ C →
          f ((p : Equiv.Perm Ω) x) = (p : Equiv.Perm Ω) (f x))) ↔
      ∃ p₀ : P, ∀ x : Ω, x ∈ C →
        f x = (p₀ : Equiv.Perm Ω) x

/-- The actual restriction map from the block kernel to the direct power of P. -/
def restrictionEmbedsIntoPower
    {Ω : Type*} (P : Subgroup (Equiv.Perm Ω))
    (B : Set (Set Ω)) (M : Subgroup (Equiv.Perm Ω))
    (K : Subgroup M) : Prop :=
  ∃ ρ : K →* (B → P),
    Function.Injective ρ ∧
      ∀ k : K, ∀ C : B, ∀ x : Ω, x ∈ (C : Set Ω) →
        ((ρ k C : P) : Equiv.Perm Ω) x =
          (((k : M) : Equiv.Perm Ω) x)

/-- A finite kernel has no prime divisors outside the Hall prime set. -/
def isAbelianPiKernel {Ω : Type*}
    (A : Type*) [Fintype A]
    (M : Subgroup (Equiv.Perm Ω)) (K : Subgroup M) : Prop :=
  (∀ k₁ k₂ : K, k₁ * k₂ = k₂ * k₁) ∧
    (∀ p : ℕ, Nat.Prime p → p ∣ Nat.card K → p ∣ Nat.card A)

/-- The subgroup product is an internal direct product. -/
def internalDirectProduct {E : Type*} [Group E]
    (P U R : Subgroup E) : Prop :=
  P ≤ R ∧ U ≤ R ∧ P ⊓ U = ⊥ ∧ P ⊔ U = R ∧
    (∀ p : P, ∀ u : U, (p : E) * (u : E) = (u : E) * (p : E))

/-- A complement to an actual kernel factors the actual middle group uniquely. -/
def complementToKernel {E : Type*} [Group E]
    (M : Subgroup E) (K : Subgroup M) (U : Subgroup E) : Prop :=
  U ≤ M ∧
    ∀ m : M, ∃! ku : K × U,
      (((ku.1 : K) : M) : E) * (ku.2 : E) = (m : E)

/-- The block action of a subgroup is an isomorphism onto the actual image. -/
def blockImageIsomorphism {Ω : Type*}
    (B : Set (Set Ω)) (U : Subgroup (Equiv.Perm Ω))
    (L : Subgroup (Equiv.Perm B)) : Prop :=
  ∃ φ : U →* L,
    Function.Bijective φ ∧
      ∀ u : U, inducesBlockPermutation B
        (u : Equiv.Perm Ω) (φ u : Equiv.Perm B)

/-- The exact kernel condition for a subgroup of the generated permutation group. -/
def exactBlockKernel {Ω : Type*}
    (M : Subgroup (Equiv.Perm Ω)) (B : Set (Set Ω))
    (K : Subgroup M) : Prop :=
  ∀ k : M, k ∈ K ↔
    ∀ C : B, (k : Equiv.Perm Ω) '' (C : Set Ω) = (C : Set Ω)

/-- Claim 47375: the aligned extension has the stated kernel, centralizer,
Hall-factor, quotient-image, and complement structure. -/
def claim47375 : Prop :=
  ∀ (A H Ω : Type*) [CommGroup A] [Group H]
    [Fintype A] [Fintype H] [Fintype Ω]
    (R T P : Subgroup (Equiv.Perm Ω))
    (B : Set (Set Ω)) (L : Subgroup (Equiv.Perm B))
    (eR : A × H ≃* R) (eT : A × H ≃* T),
    Nat.Coprime (Nat.card A) (Nat.card H) →
    alignedHallSetup A H Ω R T P B L eR eT →
    let M := Subgroup.closure
      ((R : Set (Equiv.Perm Ω)) ∪ (T : Set (Equiv.Perm Ω)))
    ∃ K : Subgroup M,
      exactBlockKernel M B K ∧
      centralizesSubgroup P R ∧
      centralizesSubgroup P T ∧
      blockCentralizerEqualsHall P B ∧
      restrictionEmbedsIntoPower P B M K ∧
      isAbelianPiKernel A M K ∧
      actualBlockImage M B L ∧
      ∃ U V : Subgroup (Equiv.Perm Ω),
        characteristicHallPiPrime R U (Nat.card A) ∧
        characteristicHallPiPrime T V (Nat.card A) ∧
        internalDirectProduct P U R ∧
        internalDirectProduct P V T ∧
        complementToKernel M K U ∧
        complementToKernel M K V ∧
        blockImageIsomorphism B U L ∧
        blockImageIsomorphism B V L

end
end MathlibPlus.Open.ResearchFormalization.R2888Claim47375
