import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The finite union-closed-family setup used by the coordinate-support claims. -/
def isUnionClosed {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∪ B ∈ 𝓕

/-- Inclusion-minimality among the nonempty members of a finite family. -/
def isMinimalNonempty {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (M : Finset α) : Prop :=
  M ∈ 𝓕 ∧ M.Nonempty ∧
    ∀ A : Finset α, A ∈ 𝓕 → A.Nonempty → A ⊆ M → A = M

/-- Four distinct members are exactly all inclusion-minimal nonempty members. -/
def exactlyFourMinimalNonempty {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (M : Fin 4 → Finset α) : Prop :=
  (∀ i, isMinimalNonempty 𝓕 (M i)) ∧
    Function.Injective M ∧
    (∀ A : Finset α, isMinimalNonempty 𝓕 A → ∃ i, A = M i)

/-- The minimum-member indices containing a coordinate. -/
def supportIndex {α : Type*} [DecidableEq α]
    (M : Fin 4 → Finset α) (x : α) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => x ∈ M i)

/-- The union of the principal filters of minima containing a coordinate. -/
def supportRegion {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (M : Fin 4 → Finset α) (x : α) :
    Finset (Finset α) :=
  𝓕.filter (fun A => ∃ i : Fin 4, i ∈ supportIndex M x ∧ M i ⊆ A)

/-- Coordinate frequency in a finite family. -/
def coordinateFrequency {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (x : α) : Nat :=
  (𝓕.filter (fun A => x ∈ A)).card

/-- R-2681.1 — coordinate-support cover lemma. -/
def claim_45102 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (𝓕 : Finset (Finset α))
    (M : Fin 4 → Finset α),
    isUnionClosed 𝓕 →
    exactlyFourMinimalNonempty 𝓕 M →
    (∀ A : Finset α, A ∈ 𝓕 → A.Nonempty → ∃ i, M i ⊆ A) ∧
    (∀ x y : α,
      supportIndex M x ∪ supportIndex M y = Finset.univ →
      let Wₓ := supportRegion 𝓕 M x
      let Wᵧ := supportRegion 𝓕 M y
      Wₓ ∪ Wᵧ = 𝓕.filter Finset.Nonempty ∧
        (Wₓ ∩ Wᵧ).Nonempty ∧
        Wₓ.card + Wᵧ.card =
          (𝓕.filter Finset.Nonempty).card + (Wₓ ∩ Wᵧ).card ∧
        2 * max Wₓ.card Wᵧ.card ≥ 𝓕.card ∧
        ((Wₓ.card ≥ Wᵧ.card ∧
            2 * coordinateFrequency 𝓕 x ≥ 𝓕.card) ∨
          (Wᵧ.card > Wₓ.card ∧
            2 * coordinateFrequency 𝓕 y ≥ 𝓕.card)))

/-- R-2681.2, the two-edge matching consequence. -/
def claim_45103 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (𝓕 : Finset (Finset α))
    (M : Fin 4 → Finset α),
    isUnionClosed 𝓕 →
    exactlyFourMinimalNonempty 𝓕 M →
    (∃ i j k l : Fin 4,
      i ≠ j ∧ k ≠ l ∧
        i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧
        (M i ∩ M j).Nonempty ∧ (M k ∩ M l).Nonempty) →
    ∃ x : α, 2 * coordinateFrequency 𝓕 x ≥ 𝓕.card

/-- The two vertices of a bipartite edge, viewed in the disjoint union of
its two coordinate blocks. -/
def edgeVertices {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (e : P × Q) : Finset (P ⊕ Q) :=
  {Sum.inl e.1, Sum.inr e.2}

/-- The vertices in the union of a finite unordered collection of edges. -/
def pairVertices {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (r : Finset (P × Q)) : Finset (P ⊕ Q) :=
  r.biUnion (fun e => edgeVertices e)

/-- The set of distinct vertex unions of two distinct edges. -/
def edgeUnions {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (E : Finset (P × Q)) : Finset (Finset (P ⊕ Q)) :=
  (E.powerset.filter (fun r => r.card = 2)).image pairVertices

/-- Unordered two-edge preimages of a vertex union. -/
def edgePairPreimages {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (E : Finset (P × Q)) (w : Finset (P ⊕ Q)) : Finset (Finset (P × Q)) :=
  E.powerset.filter (fun r => r.card = 2 ∧ pairVertices r = w)

/-- R-2688.2, the three-or-four vertex and multiplicity statement. -/
def claim_45121 : Prop :=
  ∀ {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (E : Finset (P × Q)),
    (∀ r ∈ E.powerset, r.card = 2 →
      (pairVertices r).card = 3 ∨ (pairVertices r).card = 4) ∧
    (∀ w ∈ edgeUnions E,
      ((w.card = 3 → (edgePairPreimages E w).card ≤ 1) ∧
        (w.card = 4 → (edgePairPreimages E w).card ≤ 2)))

/-- R-2688.3, the binomial count from the two-preimage bound. -/
def claim_45122 : Prop :=
  ∀ {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (E : Finset (P × Q)),
    Nat.choose E.card 2 ≤ 2 * (edgeUnions E).card

/-- R-2688.4, the resulting edge-versus-union inequality. -/
def claim_45123 : Prop :=
  ∀ {P Q : Type*} [DecidableEq P] [DecidableEq Q]
    (E : Finset (P × Q)),
    E.card ≤ (edgeUnions E).card + 1

/-- The seven distinct-or-deduplicated nonempty unions of three generators. -/
def generatedUnions {α : Type*} [DecidableEq α]
    (A B C : Finset α) : Finset (Finset α) :=
  {A, B, C, A ∪ B, A ∪ C, B ∪ C, A ∪ B ∪ C}

/-- Pairwise incomparability and nonemptiness of three generators. -/
def pairwiseIncomparable3 {α : Type*} [DecidableEq α]
    (A B C : Finset α) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
    ¬ A ⊆ B ∧ ¬ B ⊆ A ∧
    ¬ A ⊆ C ∧ ¬ C ⊆ A ∧
    ¬ B ⊆ C ∧ ¬ C ⊆ B

/-- Pairwise disjointness of three generators. -/
def pairwiseDisjoint3 {α : Type*} [DecidableEq α]
    (A B C : Finset α) : Prop :=
  A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅

/-- R-2692.4, the exact generated-family classification and equality case. -/
def claim_45141 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (A B C : Finset α),
    pairwiseIncomparable3 A B C →
    let G := generatedUnions A B C
    let H := insert ∅ G
    let S := A ∪ B ∪ C
    let overlap :=
      ∃ x : α,
        (x ∈ A ∧ x ∈ B) ∨ (x ∈ A ∧ x ∈ C) ∨ (x ∈ B ∧ x ∈ C)
    (overlap →
        (∃ x : α, 2 * coordinateFrequency G x > G.card) ∧
        (∃ x : α, 2 * coordinateFrequency H x > H.card)) ∧
      (pairwiseDisjoint3 A B C →
        G.card = 7 ∧
          (∀ x : α, x ∈ S → coordinateFrequency G x = 4) ∧
          H.card = 8 ∧
          (∀ x : α, x ∈ S →
            2 * coordinateFrequency H x = H.card)) ∧
      ((∀ x : α, x ∈ S →
          2 * coordinateFrequency H x = H.card) ↔
        pairwiseDisjoint3 A B C)

end MathlibPlus.Open.ResearchFormalizationBatch
