import Mathlib

namespace MathlibPlus.Open.Research.AdmittedBatch019ffedd

/-- The union product of two finite set families. -/
def unionProduct {α : Type} [DecidableEq α]
    (A B : Finset (Finset α)) : Finset (Finset α) :=
  A.biUnion (fun a => B.image (fun b => a ∪ b))

/-- A finite family is union-closed. -/
def unionClosed {α : Type} [DecidableEq α]
    (A : Finset (Finset α)) : Prop :=
  ∀ ⦃a b : Finset α⦄, a ∈ A → b ∈ A → a ∪ b ∈ A

/-- The total intersection of a family is empty. -/
def emptyTotalIntersection {α : Type} [DecidableEq α]
    (A : Finset (Finset α)) : Prop :=
  ∀ x : α, ∃ a ∈ A, x ∉ a

/-- The hypotheses in the five-member union-product claim. -/
def fiveMemberUnionProductHypotheses {α : Type} [DecidableEq α]
    (A B : Finset (Finset α)) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧
    (∅ : Finset α) ∉ A ∧ (∅ : Finset α) ∉ B ∧
    unionClosed A ∧ unionClosed B ∧
    emptyTotalIntersection A ∧ emptyTotalIntersection B ∧
    (unionProduct A B).card = 5

/-- Claim 21068: the five-member union-product factor cap. -/
def fiveMemberUnionProductFactorCap : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    fiveMemberUnionProductHypotheses A B →
      min A.card B.card ≤ 10

/-- The nonempty finite-intersection closure of a product family. -/
def meetClosure {α : Type} [DecidableEq α]
    (P : Finset (Finset α)) : Set (Finset α) :=
  {s | ∃ T : Finset (Finset α),
    T.Nonempty ∧ T ⊆ P ∧
      ∀ x : α, x ∈ s ↔ ∀ t ∈ T, x ∈ t}

/-- Claim 21070: product factors lie in the meet closure. -/
def factorsLieInMeetClosureOfProduct : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    fiveMemberUnionProductHypotheses A B →
      let P := unionProduct A B
      (∀ a ∈ A, a ∈ meetClosure P) ∧
        (∀ b ∈ B, b ∈ meetClosure P)

/-- Claim 21072: two large factors force a twelve-element meet closure. -/
def twoLargeFactorsForceTwelveElementMeetClosure : Prop :=
  ∀ {α : Type} [DecidableEq α] (A B : Finset (Finset α)),
    fiveMemberUnionProductHypotheses A B →
      11 ≤ A.card → 11 ≤ B.card →
      let P := unionProduct A B
      (∀ a ∈ A, a ∈ meetClosure P) ∧
        (∀ b ∈ B, b ∈ meetClosure P) ∧
        (∅ : Finset α) ∈ meetClosure P ∧
        Set.ncard (meetClosure P) ≥ 12

/-- An edge of a labelled simple graph on `Fin n`. -/
def edge (n : Nat) := {e : Finset (Fin n) // e.card = 2}

abbrev edgeSet (n : Nat) := Set (edge n)

/-- The complete labelled graph edge set. -/
def completeEdgeSet (n : Nat) : edgeSet n := Set.univ

/-- The edge joining two distinct labelled vertices. -/
def edgeBetween {n : Nat} (u v : Fin n) (h : u ≠ v) : edge n :=
  ⟨{u, v}, by simp [h]⟩

/-- Incidence of a vertex with an edge. -/
def incident {n : Nat} (v : Fin n) (e : edge n) : Prop :=
  v ∈ e.1

/-- Addition in the Boolean edge space, written as symmetric difference. -/
def booleanEdgeAddition {n : Nat} (A B : edgeSet n) : edgeSet n :=
  {e | (e ∈ A ∧ e ∉ B) ∨ (e ∈ B ∧ e ∉ A)}

/-- A vertex is isolated in an edge set. -/
def isolatedAt {n : Nat} (v : Fin n) (A : edgeSet n) : Prop :=
  ∀ e ∈ A, v ∉ e.1

/-- The isolate-bearing sector of the Boolean edge space. -/
def isolateSector (n : Nat) : Set (edgeSet n) :=
  {A | ∃ v : Fin n, isolatedAt v A}

abbrev booleanEdgeSpace (n : Nat) := edgeSet n

/-- Claim 21110: the Boolean edge space and its isolate sector. -/
def booleanEdgeSpaceAndIsolateSector : Prop :=
  ∀ n : Nat,
    (∀ A B : booleanEdgeSpace n,
      booleanEdgeAddition A B =
        {e | (e ∈ A ∧ e ∉ B) ∨ (e ∈ B ∧ e ∉ A)}) ∧
    (isolateSector n =
      {A : edgeSet n | ∃ v : Fin n, ∀ e ∈ A, v ∉ e.1})

/-- Claim 21112: factorization across a chosen missing edge. -/
def missingEdgeFactorizationOfNoncompleteGraph : Prop :=
  ∀ (n : Nat) (C : edgeSet n),
    C ≠ completeEdgeSet n →
      ∀ (u v : Fin n) (h : u ≠ v),
        edgeBetween u v h ∉ C →
          let A : edgeSet n := {e | e ∈ C ∧ incident v e}
          let B := booleanEdgeAddition C A
          isolatedAt u A ∧ isolatedAt v B ∧ booleanEdgeAddition A B = C

/-- The pairwise symmetric-difference square of a sector. -/
def xorSquare {n : Nat} (S : Set (edgeSet n)) : Set (edgeSet n) :=
  {C | ∃ A ∈ S, ∃ B ∈ S, booleanEdgeAddition A B = C}

/-- Claim 21113: the isolate-sector xor square omits exactly the complete graph. -/
def isolateSectorExactXorSquare : Prop :=
  ∀ n : Nat, 2 ≤ n →
    xorSquare (isolateSector n) =
      {C : edgeSet n | C ≠ completeEdgeSet n}

/-- The complement of an edge set relative to the complete graph. -/
def edgeComplement {n : Nat} (C : edgeSet n) : edgeSet n :=
  {e | e ∉ C}

/-- An edge set is a matching when distinct edges are vertex-disjoint. -/
def isMatching {n : Nat} (D : edgeSet n) : Prop :=
  ∀ ⦃e f : edge n⦄, e ∈ D → f ∈ D → e ≠ f → Disjoint e.1 f.1

/-- A factor has at least two isolated vertices. -/
def hasAtLeastTwoIsolated {n : Nat} (A : edgeSet n) : Prop :=
  ∃ u v : Fin n, u ≠ v ∧ isolatedAt u A ∧ isolatedAt v A

/-- A factor has exactly one isolated vertex. -/
def hasExactlyOneIsolated {n : Nat} (A : edgeSet n) : Prop :=
  ∃ u : Fin n, isolatedAt u A ∧ ∀ v : Fin n, isolatedAt v A → v = u

/-- Claim 21120: the refined overlap classification for an isolate-sector factorization. -/
def refinedOverlapClassification : Prop :=
  ∀ (n : Nat) (C : edgeSet n),
    ((∃ A B : edgeSet n,
        A ∈ isolateSector n ∧ B ∈ isolateSector n ∧
          booleanEdgeAddition A B = C ∧
          (hasAtLeastTwoIsolated A ∨ hasAtLeastTwoIsolated B)) ↔
      ¬ isMatching (edgeComplement C)) ∧
    (isMatching (edgeComplement C) →
      ∀ A B : edgeSet n,
        A ∈ isolateSector n → B ∈ isolateSector n →
        booleanEdgeAddition A B = C →
        hasExactlyOneIsolated A ∧ hasExactlyOneIsolated B)

end MathlibPlus.Open.Research.AdmittedBatch019ffedd
