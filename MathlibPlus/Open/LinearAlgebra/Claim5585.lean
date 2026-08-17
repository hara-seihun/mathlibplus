import MathlibPlus.Open.LinearAlgebra.CoordinateCertificateConnectivity

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.Claim5585

private def rowBlockSpace {F R S B : Type*} [Field F]
    (A : Matrix R S F) (rowBlock : B → Set R) (b : B) :
    Submodule F (S → F) :=
  Submodule.span F
    ((fun r : R => fun s : S => A r s) '' rowBlock b)

private def blockCoordinateSupport {F R S B : Type*} [Field F]
    (A : Matrix R S F) (rowBlock : B → Set R) (b : B) : Set S :=
  {s | ∃ r, r ∈ rowBlock b ∧ A r s ≠ 0}

private def blockIntersectionAdjacent {F R S B : Type*} [Field F]
    (A : Matrix R S F) (rowBlock : B → Set R) (b c : B) : Prop :=
  (blockCoordinateSupport A rowBlock b ∩
      blockCoordinateSupport A rowBlock c).Nonempty

private def componentImage {F S B : Type*} [Field F]
    (components : Finset B) (u : B → S → F) : S → F :=
  Finset.sum components u

private def coordinateSupport {F S : Type*} [Field F]
    (z : S → F) : Set S :=
  {s | z s ≠ 0}

private def targetCoordinateVector {F S : Type*} [Field F] [DecidableEq S]
    (t : S) (alpha : F) : S → F :=
  fun s => if s = t then alpha else 0

private def connectedComponentPartition
    {F R S B : Type*} [Field F]
    (A : Matrix R S F) (rowBlock : B → Set R)
    (J : Finset B) {m : ℕ}
    (components : Fin m → Finset B) : Prop :=
  (∀ i : Fin m,
    (components i).Nonempty ∧ components i ⊆ J) ∧
    (∀ i j : Fin m, i ≠ j →
      Disjoint (components i) (components j)) ∧
    (∀ b : B, b ∈ J ↔ ∃ i : Fin m, b ∈ components i) ∧
    (∀ i : Fin m, ∀ b c : B,
      b ∈ components i → c ∈ components i →
      Relation.ReflTransGen
        (fun x y : B =>
          x ∈ J ∧ y ∈ J ∧
            blockIntersectionAdjacent A rowBlock x y) b c) ∧
    (∀ b c : B, b ∈ J → c ∈ J →
      Relation.ReflTransGen
        (fun x y : B =>
          x ∈ J ∧ y ∈ J ∧
            blockIntersectionAdjacent A rowBlock x y) b c →
      ∃ i : Fin m, b ∈ components i ∧ c ∈ components i)

/-- Claim 5585: for an actual matrix row-block arrangement, a supplied
connected-component partition of a block-supported coordinate certificate has
pairwise disjoint component-image coordinate supports, and all blocks meeting
the target coordinate lie in one target component. -/
def componentImagesDisjointAndTargetComponent_claim5585 : Prop :=
  ∀ {F R S B : Type*} [Field F] [Fintype R] [Fintype S]
    [Fintype B] [DecidableEq B] [DecidableEq S]
    (A : Matrix R S F) (rowBlock : B → Set R),
    ((∀ ⦃b c : B⦄, b ≠ c →
        Disjoint (rowBlock b) (rowBlock c)) ∧
      (⋃ b : B, rowBlock b) = Set.univ) →
    ∀ (t : S) (J : Finset B) (u : B → S → F) (alpha : F),
      (∀ b ∈ J,
        u b ∈ rowBlockSpace A rowBlock b) →
      alpha ≠ 0 →
      Finset.sum J u = targetCoordinateVector t alpha →
      ∀ (m : ℕ) (components : Fin m → Finset B),
        connectedComponentPartition A rowBlock J components →
          (∀ i j : Fin m, i ≠ j →
            Disjoint
              (coordinateSupport (componentImage (components i) u))
              (coordinateSupport (componentImage (components j) u))) ∧
            ∃ i₀ : Fin m,
              (∃ b : B, b ∈ components i₀ ∧
                t ∈ blockCoordinateSupport A rowBlock b) ∧
              (∀ b : B, b ∈ J →
                t ∈ blockCoordinateSupport A rowBlock b →
                b ∈ components i₀)

end MathlibPlus.Open.LinearAlgebra.Claim5585
