import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.FixedPointFreeOrderThreeLift

/-- The cyclic quotient of order three, written as a multiplicative synonym for `ZMod 3` so
that it can be used by Mathlib's group-theoretic semidirect product. -/
abbrev C3 := Multiplicative (ZMod 3)

/-- The quotient coordinate corresponding to the residue `i`. -/
def c3Layer (i : ZMod 3) : C3 := Multiplicative.ofAdd i

/-- An inverse-closed connection set in a group. -/
def InverseClosed {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ ⦃s : G⦄, s ∈ S → s⁻¹ ∈ S

/-- A connection set avoiding the identity. -/
def OmitsIdentity {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ ⦃s : G⦄, s ∈ S → s ≠ 1

/-- The undirected Cayley graph associated to a connection set. -/
def CayleyGraph (G : Type*) [Group G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel (fun x y => ∃ s ∈ S, y = x * s)

/-- The kernel-layer predicate in the semidirect-product coordinates. -/
def KernelLayer {M : Type*} [Group M] (φ : C3 →* MulAut M) (S : Set M) :
    Set (M ⋊[φ] C3) :=
  {g | g.right = (1 : C3) ∧ g.left ∈ S}

/-- A complete quotient layer in the semidirect-product coordinates. -/
def QuotientLayer {M : Type*} [Group M] (φ : C3 →* MulAut M) (i : C3) :
    Set (M ⋊[φ] C3) :=
  {g | g.right = i}

/-- The full nonidentity-layer lift of a kernel connection set. -/
def LiftedConnectionSet {M : Type*} [Group M] (φ : C3 →* MulAut M) (S : Set M) :
    Set (M ⋊[φ] C3) :=
  KernelLayer φ S ∪ QuotientLayer φ (c3Layer 1) ∪ QuotientLayer φ (c3Layer 2)

/-- The fixed-point-free order-three action datum used by all seven claims.  The
multiplicative notation is the standard recoding of the additive notation in the packet. -/
def SemidirectExtensionHypotheses
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M) : Prop :=
  orderOf θ = 3 ∧
  (∀ x : M, θ x = x → x = 1) ∧
  φ (c3Layer 1) = θ ∧
  InverseClosed S ∧ InverseClosed T ∧
  OmitsIdentity S ∧ OmitsIdentity T ∧
  Nonempty (CayleyGraph M S ≃g CayleyGraph M T) ∧
  ¬∃ β : MulAut M, Set.image β S = T

/-- Claim 59206: the exact fixed-point-free order-three semidirect-extension setup
with a non-CI inverse-closed kernel pair. -/
def claim59206
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M) : Prop :=
  SemidirectExtensionHypotheses M θ φ S T

/-- Claim 59207: the two complete nonidentity quotient layers are added to each
kernel connection set, with the displayed valencies. -/
def claim59207
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M)
    (_h : SemidirectExtensionHypotheses M θ φ S T) : Prop :=
  let S_hat := LiftedConnectionSet φ S
  let T_hat := LiftedConnectionSet φ T
  Set.ncard S_hat = Set.ncard S + 2 * Fintype.card M ∧
    Set.ncard T_hat = Set.ncard T + 2 * Fintype.card M

/-- The explicit theta-twisted layer map from Claim 59208. -/
def ThetaTwistedLayerMap
    {M : Type*} [CommGroup M] [Fintype M]
    (φ : C3 →* MulAut M)
    {S T : Set M} (f : CayleyGraph M S ≃g CayleyGraph M T)
    (g : M ⋊[φ] C3) : M ⋊[φ] C3 :=
  ⟨φ g.right (f (φ g.right⁻¹ g.left)), g.right⟩

/-- Claim 59208: the displayed theta-twisted layer map is a bijective graph
isomorphism for the lifted connection sets. -/
def claim59208
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M)
    (_h : SemidirectExtensionHypotheses M θ φ S T)
    (f : CayleyGraph M S ≃g CayleyGraph M T) : Prop :=
  let F := ThetaTwistedLayerMap φ f
  Function.Bijective F ∧
    ∀ x y : M ⋊[φ] C3,
      (CayleyGraph (M ⋊[φ] C3) (LiftedConnectionSet φ T)).Adj (F x) (F y) ↔
        (CayleyGraph (M ⋊[φ] C3) (LiftedConnectionSet φ S)).Adj x y

/-- Claim 59209: both full-layer lifts are connected. -/
def claim59209
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M)
    (_h : SemidirectExtensionHypotheses M θ φ S T) : Prop :=
  (CayleyGraph (M ⋊[φ] C3) (LiftedConnectionSet φ S)).Connected ∧
    (CayleyGraph (M ⋊[φ] C3) (LiftedConnectionSet φ T)).Connected

/-- Claim 59210: inverse closure is preserved by the paired nonidentity layers,
and the lifted connection sets have the stated and equal valencies. -/
def claim59210
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M)
    (_h : SemidirectExtensionHypotheses M θ φ S T) : Prop :=
  InverseClosed (KernelLayer φ S) ∧
  InverseClosed (KernelLayer φ T) ∧
  InverseClosed (QuotientLayer φ (c3Layer 1) ∪ QuotientLayer φ (c3Layer 2)) ∧
  InverseClosed (LiftedConnectionSet φ S) ∧
  InverseClosed (LiftedConnectionSet φ T) ∧
  Set.ncard S = Set.ncard T ∧
  Set.ncard (LiftedConnectionSet φ S) = Set.ncard S + 2 * Fintype.card M ∧
  Set.ncard (LiftedConnectionSet φ T) = Set.ncard T + 2 * Fintype.card M ∧
  Set.ncard (LiftedConnectionSet φ S) = Set.ncard (LiftedConnectionSet φ T)

/-- The multiplicative recoding of the additive map `theta - 1`. -/
def ThetaMinusIdentity {M : Type*} [CommGroup M] (θ : MulAut M) (x : M) : M :=
  θ x * x⁻¹

/-- Claim 59211: fixed-point-freeness identifies the characteristic derived kernel
and forces every extension automorphism carrying the lifted sets to restrict to a
kernel automorphism carrying `S` to `T`. -/
def claim59211
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M)
    (_h : SemidirectExtensionHypotheses M θ φ S T) : Prop :=
  let G := M ⋊[φ] C3
  let K := (SemidirectProduct.inl : M →* G).range
  let S_hat := LiftedConnectionSet φ S
  let T_hat := LiftedConnectionSet φ T
  Function.Injective (ThetaMinusIdentity θ) ∧
  Function.Bijective (ThetaMinusIdentity θ) ∧
  commutator G = K ∧
  K.Characteristic ∧
  (∀ α : G ≃* G, Set.image α S_hat = T_hat →
    ∃ β : MulAut M,
      (∀ x : M,
        α (SemidirectProduct.inl x : G) =
          (SemidirectProduct.inl (β x) : G)) ∧
      Set.image β S = T) ∧
  ¬∃ α : G ≃* G, Set.image α S_hat = T_hat

/-- Claim 59212: the hypotheses yield connected, inverse-closed, isomorphic
ordinary Cayley graphs of equal valency, with no extension-group automorphism
carrying one lifted set to the other. -/
def claim59212
    (M : Type*) [CommGroup M] [Fintype M]
    (θ : MulAut M) (φ : C3 →* MulAut M) (S T : Set M)
    (_h : SemidirectExtensionHypotheses M θ φ S T) : Prop :=
  let G := M ⋊[φ] C3
  let S_hat := LiftedConnectionSet φ S
  let T_hat := LiftedConnectionSet φ T
  (CayleyGraph G S_hat).Connected ∧
  (CayleyGraph G T_hat).Connected ∧
  InverseClosed S_hat ∧
  InverseClosed T_hat ∧
  Nonempty (CayleyGraph G S_hat ≃g CayleyGraph G T_hat) ∧
  Set.ncard S_hat = Set.ncard S + 2 * Fintype.card M ∧
  Set.ncard T_hat = Set.ncard T + 2 * Fintype.card M ∧
  Set.ncard S_hat = Set.ncard T_hat ∧
  ¬∃ α : G ≃* G, Set.image α S_hat = T_hat

end MathlibPlus.Open.FormalizationBatch.FixedPointFreeOrderThreeLift
