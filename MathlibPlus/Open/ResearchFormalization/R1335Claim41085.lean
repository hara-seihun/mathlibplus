import MathlibPlus.Open.ResearchFormalization.BatchGraphClaim

namespace MathlibPlus.Open.ResearchFormalization.R1335

namespace Claim41085

noncomputable section

abbrev F5 := ZMod 5

/-- Translation by an exponent in the fixed semiregular `C₅` action. -/
def rotationBy {X : Type*} (a : F5) : Equiv.Perm (F5 × X) :=
  Equiv.prodCongr (Equiv.addRight a) (Equiv.refl X)

abbrev rotation {X : Type*} : Equiv.Perm (F5 × X) :=
  rotationBy 1

/-- The normalizer of the fixed rotation, expressed by its nonzero exponent. -/
def normalizesRotation {X : Type*}
    (f : Equiv.Perm (F5 × X)) : Prop :=
  ∃ lam : F5, lam ≠ 0 ∧
    f * rotation * f.symm = rotationBy lam

/-- Direct adjacency preservation by a permutation of the graph carrier. -/
def graphAutomorphism {X : Type*}
    (Γ : SimpleGraph (F5 × X)) (f : Equiv.Perm (F5 × X)) : Prop :=
  ∀ u v, Γ.Adj (f u) (f v) ↔ Γ.Adj u v

/-- The induced action on the `P`-orbit index set. -/
def inducesBlockPermutation {X : Type*}
    (f : Equiv.Perm (F5 × X)) (σ : Equiv.Perm X) : Prop :=
  ∀ z : F5, ∀ x : X, (f (z, x)).2 = σ x

/-- The complete affine voltage switching equation. -/
def switchingEquation {X : Type*}
    (Γ : SimpleGraph (F5 × X)) (σ : Equiv.Perm X)
    (lam : F5) (τ : X → F5) : Prop :=
  ∀ x y : X,
    vSet Γ (σ x) (σ y) =
      (fun d : F5 => lam * d + τ y - τ x) '' vSet Γ x y

/-- The actual image on the `P`-orbits of graph automorphisms normalizing `P`. -/
def actualNormalizerImage {X : Type*}
    (Γ : SimpleGraph (F5 × X)) : Set (Equiv.Perm X) :=
  {σ | ∃ f : Equiv.Perm (F5 × X),
    graphAutomorphism Γ f ∧ normalizesRotation f ∧
      inducesBlockPermutation f σ}

/-- The projection of the global affine switching stabilizer. -/
def affineSwitchingProjection {X : Type*}
    (Γ : SimpleGraph (F5 × X)) : Set (Equiv.Perm X) :=
  {σ | ∃ lam : F5, lam ≠ 0 ∧ ∃ τ : X → F5,
    switchingEquation Γ σ lam τ}

/-- Claim 41085: under the stated `P`-invariance, the actual induced image is
exactly the affine switching projection. -/
def actualNormalizerImage_claim41085 : Prop :=
  ∀ {X : Type*} [Fintype X]
    (Γ : SimpleGraph (F5 × X)),
    PInvariantGraph Γ →
      actualNormalizerImage Γ = affineSwitchingProjection Γ

end

end Claim41085

end MathlibPlus.Open.ResearchFormalization.R1335
