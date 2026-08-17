import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2900

/-- Automorphisms of a family of binary relations on a finite carrier. -/
def relationalAutomorphism {J V : Type*}
    (relations : J → V → V → Prop) (f : Equiv.Perm V) : Prop :=
  ∀ j x y, relations j x y ↔ relations j (f x) (f y)

/-- Regularity of a permutation subgroup, with the acting group retained. -/
def regularPermutationCopy {H V : Type*} [Group H]
    (R : Subgroup (Equiv.Perm V)) (e : H ≃* R) : Prop :=
  ∀ x y : V, ∃! h : H, ((e h : R) : Equiv.Perm V) x = y

/-- The unique nonidentity involution of a group. -/
def uniqueNontrivialInvolution {G : Type*} [Group G] (z : G) : Prop :=
  z ≠ 1 ∧ z ^ (2 : ℕ) = 1 ∧
    ∀ u : G, u ≠ 1 → u ^ (2 : ℕ) = 1 → u = z

/-- The orbit of a point under a subgroup transported to permutations. -/
def transportedOrbit {H V : Type*} [Group H]
    (action : H →* Equiv.Perm V) (K : Subgroup H) (x : V) : Set V :=
  {y | ∃ k : K, action (k : H) x = y}

/-- Equality between a transported orbit partition and an indexed block partition. -/
def hasIndexedOrbitPartition {H V B : Type*} [Group H]
    (action : H →* Equiv.Perm V) (K : Subgroup H)
    (blocks : B → Set V) : Prop :=
  ∀ U : Set V,
    (∃ x : V, transportedOrbit action K x = U) ↔
      (∃ b : B, blocks b = U)

/-- A cyclic characteristic subgroup of the generalized quaternion group. -/
def characteristicCyclicQuaternionSubgroup (n : ℕ)
    (K : Subgroup (QuaternionGroup n)) : Prop :=
  IsCyclic K ∧ Nat.card K = n ∧
    ∀ φ : QuaternionGroup n ≃* QuaternionGroup n,
      Subgroup.map φ.toMonoidHom K = K

/-- A four-block partition indexed by a finite block carrier. -/
def fourOddBlockPartition {V B : Type*} [Fintype V] [Fintype B]
    (blocks : B → Set V) (n : ℕ) : Prop :=
  Fintype.card B = 4 ∧ Odd n ∧
    (∀ b : B, (blocks b).Nonempty ∧ (blocks b).ncard = n) ∧
    (∀ b₁ b₂ : B, b₁ ≠ b₂ → Disjoint (blocks b₁) (blocks b₂)) ∧
    (⋃ b : B, blocks b) = Set.univ

/-- The regular cyclic order-four action induced on the four blocks.  The last
clause identifies the image of the quaternionic central involution with the
square of an actual four-cycle in the actual image. -/
def regularCyclicFourBlockAction {H B : Type*} [Group H] [Fintype B]
    (action : H →* Equiv.Perm B) (z : H) : Prop :=
  let X := MonoidHom.range action
  (∀ x y : B, ∃! g : X, (g : Equiv.Perm B) x = y) ∧
    Nat.card X = 4 ∧
    ∃ c : Equiv.Perm B,
      c ∈ X ∧ orderOf c = 4 ∧
        Subgroup.closure ({c} : Set (Equiv.Perm B)) = X ∧
        action z = c ^ (2 : ℕ)

/-- A concrete setup for the quaternion block argument.  The block action is a
monoid hom from the given automorphism group, and its displayed equation makes
it the actual action on the named blocks rather than an abstract quotient
permutation. -/
def quaternionBlockSetup
    {J V B : Type*} [Fintype V] [Fintype B]
    (relations : J → V → V → Prop)
    (A : Subgroup (Equiv.Perm V))
    (blocks : B → Set V) (n : ℕ)
    (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (eR : QuaternionGroup n ≃* R) (eT : QuaternionGroup n ≃* T)
    (CR CT : Subgroup (QuaternionGroup n))
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B) : Prop :=
  (∀ f : Equiv.Perm V,
    f ∈ A ↔ relationalAutomorphism relations f) ∧
  fourOddBlockPartition blocks n ∧
  (∀ a : A, ∀ b : B,
    blocks (blockAction a b) = (a : Equiv.Perm V) '' blocks b) ∧
  R ≤ A ∧ T ≤ A ∧
  regularPermutationCopy R eR ∧
  regularPermutationCopy T eT ∧
  characteristicCyclicQuaternionSubgroup n CR ∧
  characteristicCyclicQuaternionSubgroup n CT ∧
  hasIndexedOrbitPartition
    (R.subtype.comp eR.toMonoidHom) CR blocks ∧
  hasIndexedOrbitPartition
    (T.subtype.comp eT.toMonoidHom) CT blocks ∧
  uniqueNontrivialInvolution zR ∧
  uniqueNontrivialInvolution zT ∧
  regularCyclicFourBlockAction
    (blockAction.comp (Subgroup.inclusion hR)) zR ∧
  regularCyclicFourBlockAction
    (blockAction.comp (Subgroup.inclusion hT)) zT

/-- Conjugacy witnessed inside a permutation subgroup. -/
def conjugateInSubgroup {G : Type*} [Group G]
    (X : Subgroup G) (a b : G) : Prop :=
  ∃ x : X, (x : G)⁻¹ * a * (x : G) = b

/-- A binary signature preserved by a permutation. -/
def preservesBinarySignature {B : Type*}
    (signature : B → B → Prop) (g : Equiv.Perm B) : Prop :=
  ∀ x y, signature x y ↔ signature (g x) (g y)

/-- The finite four-cycle census and the subgroup square-conjugacy statement. -/
def fourCycleSquareCensusClaim : Prop :=
  Nat.card {r : Equiv.Perm (Fin 4) // orderOf r = 4} = 6 ∧
  Nat.card {p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) //
    orderOf p.1 = 4 ∧ orderOf p.2 = 4} = 36 ∧
  (∀ (X : Subgroup (Equiv.Perm (Fin 4)))
      (r t : Equiv.Perm (Fin 4)),
    r ∈ X → t ∈ X → orderOf r = 4 → orderOf t = 4 →
      conjugateInSubgroup X (r ^ (2 : ℕ)) (t ^ (2 : ℕ)) ∧
        (r ^ (2 : ℕ) = t ^ (2 : ℕ) ∨
          Subgroup.closure ({r, t} : Set (Equiv.Perm (Fin 4))) = ⊤))

/-- The block-image application of the four-cycle lemma, including every
binary signature invariant under the actual induced image. -/
def blockSquareConjugacyConclusion
    {V B : Type*} [Fintype V] [Fintype B]
    (A : Subgroup (Equiv.Perm V))
    (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B) : Prop :=
  let ρR := blockAction.comp (Subgroup.inclusion hR)
  let ρT := blockAction.comp (Subgroup.inclusion hT)
  let X := MonoidHom.range blockAction
  ∃ x : X,
    (x : Equiv.Perm B)⁻¹ * ρR zR * (x : Equiv.Perm B) = ρT zT ∧
    ∀ signature : B → B → Prop,
      (∀ g : X, preservesBinarySignature signature (g : Equiv.Perm B)) →
        preservesBinarySignature signature (x : Equiv.Perm B)

/-- Claim 47399. -/
def claim47399 : Prop :=
  fourCycleSquareCensusClaim ∧
  (∀ (J V B : Type*) [Fintype V] [Fintype B]
      (relations : J → V → V → Prop)
      (A : Subgroup (Equiv.Perm V))
      (blocks : B → Set V) (n : ℕ)
      (R T : Subgroup (Equiv.Perm V))
      (hR : R ≤ A) (hT : T ≤ A)
      (eR : QuaternionGroup n ≃* R) (eT : QuaternionGroup n ≃* T)
      (CR CT : Subgroup (QuaternionGroup n))
      (zR : R) (zT : T)
      (blockAction : A →* Equiv.Perm B),
    quaternionBlockSetup relations A blocks n R T hR hT eR eT CR CT zR zT
        blockAction →
      blockSquareConjugacyConclusion A R T hR hT zR zT blockAction)

/-- The conclusion of the odd-product lift, with the block action equality as
its only post-lifting assumption. -/
def oddProductLiftConclusion
    {V B : Type*} [Fintype V] [Fintype B]
    (A : Subgroup (Equiv.Perm V))
    (blocks : B → Set V) (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B) : Prop :=
  ((blockAction.comp (Subgroup.inclusion hR)) zR =
      (blockAction.comp (Subgroup.inclusion hT)) zT) →
  let zRp : Equiv.Perm V := zR
  let zTp : Equiv.Perm V := zT
  let w : Equiv.Perm V := zRp * zTp
  w ∈ A ∧
    (∀ b : B, w '' blocks b = blocks b) ∧
    zRp * w * zRp = w⁻¹ ∧
    zTp = zRp * w ∧
    let d := orderOf w
    Odd d →
      let k := w ^ ((d - 1) / 2)
      k ∈ A ∧
        (∀ b : B, k '' blocks b = blocks b) ∧
        k⁻¹ * zTp * k = zRp

/-- Claim 47400. -/
def claim47400 : Prop :=
  ∀ (J V B : Type*) [Fintype V] [Fintype B]
    (relations : J → V → V → Prop)
    (A : Subgroup (Equiv.Perm V))
    (blocks : B → Set V) (n : ℕ)
    (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (eR : QuaternionGroup n ≃* R) (eT : QuaternionGroup n ≃* T)
    (CR CT : Subgroup (QuaternionGroup n))
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B),
    quaternionBlockSetup relations A blocks n R T hR hT eR eT CR CT zR zT
        blockAction →
      oddProductLiftConclusion A blocks R T hR hT zR zT blockAction

/-- A quotient map whose fibres are exactly the two-point orbits of a fixed-point-free involution. -/
def twoPointOrbitQuotient {V Ω : Type*}
    (z : Equiv.Perm V) (q : V → Ω) : Prop :=
  Function.Surjective q ∧
    (∀ x : V, z x ≠ x) ∧
    (∀ x y : V, q x = q y ↔ y = x ∨ y = z x)

/-- Conjugacy of the two quotient actions through an element whose block action
is in the actual image. -/
def quotientCopiesConjugateInActualImage
    {V Ω B : Type*}
    (A : Subgroup (Equiv.Perm V))
    (R T : Subgroup (Equiv.Perm V))
    (blockAction : A →* Equiv.Perm B)
    (q : V → Ω) (a : A) : Prop :=
  blockAction a ∈ MonoidHom.range blockAction ∧
  (∃ aq : Equiv.Perm Ω, ∀ x : V, aq (q x) = q ((a : Equiv.Perm V) x)) ∧
  (∀ t : T, ∃ r : R, ∀ x : V,
    q ((a : Equiv.Perm V) ((t : Equiv.Perm V) x)) =
      q ((r : Equiv.Perm V) ((a : Equiv.Perm V) x))) ∧
  (∀ r : R, ∃ t : T, ∀ x : V,
    q ((a : Equiv.Perm V) ((t : Equiv.Perm V) x)) =
      q ((r : Equiv.Perm V) ((a : Equiv.Perm V) x)))

/-- A literal common central involution of the two quaternion copies. -/
def commonLiteralCentralInvolution
    {V : Type*} (R T : Subgroup (Equiv.Perm V)) (z : Equiv.Perm V) : Prop :=
  z ∈ R ∧ z ∈ T ∧ z ≠ 1 ∧ z ^ (2 : ℕ) = 1 ∧
    (∀ r : R, z * (r : Equiv.Perm V) = (r : Equiv.Perm V) * z) ∧
    (∀ t : T, z * (t : Equiv.Perm V) = (t : Equiv.Perm V) * z) ∧
    (∀ r : R, r ≠ 1 → (r : Equiv.Perm V) ^ (2 : ℕ) = 1 →
      (r : Equiv.Perm V) = z) ∧
    (∀ t : T, t ≠ 1 → (t : Equiv.Perm V) ^ (2 : ℕ) = 1 →
      (t : Equiv.Perm V) = z)

/-- Conjugacy of the two regular copies inside the actual automorphism group. -/
def conjugateCopiesInAutomorphismGroup
    {V : Type*} (A : Subgroup (Equiv.Perm V))
    (R T : Subgroup (Equiv.Perm V)) : Prop :=
  ∃ a : A, ∀ g : Equiv.Perm V,
    g ∈ T ↔ ∃ r : Equiv.Perm V,
      r ∈ R ∧ g = (a : Equiv.Perm V)⁻¹ * r * (a : Equiv.Perm V)

/-- Claim 47401. -/
def claim47401 : Prop :=
  ∀ (J V B : Type*) [Fintype V] [Fintype B]
    (relations : J → V → V → Prop)
    (A : Subgroup (Equiv.Perm V))
    (blocks : B → Set V) (n : ℕ)
    (R T : Subgroup (Equiv.Perm V))
    (hR : R ≤ A) (hT : T ≤ A)
    (eR : QuaternionGroup n ≃* R) (eT : QuaternionGroup n ≃* T)
    (CR CT : Subgroup (QuaternionGroup n))
    (zR : R) (zT : T)
    (blockAction : A →* Equiv.Perm B)
    (z : Equiv.Perm V),
    quaternionBlockSetup relations A blocks n R T hR hT eR eT CR CT zR zT
        blockAction →
      commonLiteralCentralInvolution R T z →
      ∀ Ω : Type*, ∀ q : V → Ω,
        twoPointOrbitQuotient z q →
        (∃ a : A,
          quotientCopiesConjugateInActualImage A R T blockAction q a) →
        conjugateCopiesInAutomorphismGroup A R T

end MathlibPlus.Open.ResearchFormalization.R2900
