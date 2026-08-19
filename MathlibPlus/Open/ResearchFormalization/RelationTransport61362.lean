import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.RelationTransport61362

/-- The coordinatewise map induced by a map on the underlying carrier. -/
def coordinateMap {X Y : Type*} (u : X → Y) (k : ℕ) :
    (Fin k → X) → (Fin k → Y) :=
  fun z i => u (z i)

/-- The coordinatewise action of a group element on a tuple. -/
def coordinateAction {G X : Type*} [SMul G X] (g : G) (k : ℕ)
    (z : Fin k → X) : Fin k → X :=
  fun i => g • z i

/-- The setwise stabilizer of a relation under the coordinatewise action. -/
def relationStabilizer {G X : Type*} [Group G] [MulAction G X]
    (k : ℕ) (R : Set (Fin k → X)) : Set G :=
  {g | ∀ z, z ∈ R ↔ coordinateAction g k z ∈ R}

/-- The common stabilizer of a finite family of relations. -/
def relationFamilyStabilizer {G X I : Type*} [Group G] [MulAction G X]
    (k : ℕ) (R : I → Set (Fin k → X)) : Set G :=
  ⋂ i, relationStabilizer k (R i)

/-- The coordinatewise inverse-image statement, including its
surjective invariance equivalence. -/
def coordinateTransportStatement {X Y : Type*} (q : X → Y)
    (e : X ≃ X) (f : Y ≃ Y) : Prop :=
  Function.comp q e = Function.comp f q →
    ∀ (k : ℕ) (R : Set (Fin k → Y)),
      coordinateMap e k '' (coordinateMap q k ⁻¹' R) =
          coordinateMap q k ⁻¹' (coordinateMap f k '' R) ∧
        (Function.Surjective q →
          Function.Surjective (coordinateMap q k) ∧
            (coordinateMap e k '' (coordinateMap q k ⁻¹' R) =
                coordinateMap q k ⁻¹' R ↔
              coordinateMap f k '' R = R))

/-- The point-stabilizer part of the group-action statement. -/
def groupTransportStatement {G H X Y : Type*} [Group G] [Group H]
    [MulAction G X] [MulAction H Y] (q : X → Y) (φ : G →* H) : Prop :=
  Function.Surjective q →
    (∀ g x, q (g • x) = φ g • q x) →
      ∀ (k : ℕ) (R : Set (Fin k → Y)),
        relationStabilizer k (coordinateMap q k ⁻¹' R) =
          φ ⁻¹' relationStabilizer k R

/-- The common-stabilizer part for a labelled finite relation family. -/
def groupTransportFamilyStatement
    {G H X Y I : Type*} [Group G] [Group H] [MulAction G X]
    [MulAction H Y] (q : X → Y) (φ : G →* H) : Prop :=
  Function.Surjective q →
    (∀ g x, q (g • x) = φ g • q x) →
      ∀ (k : ℕ) (Rs : I → Set (Fin k → Y)),
        relationFamilyStabilizer k
            (fun i => coordinateMap q k ⁻¹' (Rs i)) =
          φ ⁻¹' relationFamilyStabilizer k Rs

/-- Claim 61362: all coordinatewise, group-action, and finite-family assertions. -/
def claim61362 : Prop :=
  (∀ (X Y : Type*) (q : X → Y) (e : X ≃ X) (f : Y ≃ Y),
      coordinateTransportStatement q e f) ∧
    ∀ (G H X Y : Type*) [Group G] [Group H] [MulAction G X]
      [MulAction H Y] (q : X → Y) (φ : G →* H),
      groupTransportStatement q φ ∧
        ∀ (I : Type*) [Fintype I],
          groupTransportFamilyStatement (I := I) q φ

end MathlibPlus.Open.ResearchFormalization.RelationTransport61362
