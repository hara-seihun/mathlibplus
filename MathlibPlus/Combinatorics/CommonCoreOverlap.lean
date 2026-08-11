import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

namespace MathlibPlus.Combinatorics.CommonCoreOverlap

/-- Claim 20024: an explicit common-core overlap witness whose nine cross-unions
are distinct even though each family is union-closed, empty-free, and has empty
intersection. -/
theorem commonCoreOverlapExample :
    let Vertex := Fin 5
    let z : Vertex := 0
    let a : Vertex := 1
    let b : Vertex := 2
    let c : Vertex := 3
    let d : Vertex := 4
    let familyA : Finset (Finset Vertex) := {{z, a}, {b}, {z, a, b}}
    let familyB : Finset (Finset Vertex) := {{z, c}, {d}, {z, c, d}}
    let UnionClosed : Finset (Finset Vertex) → Prop :=
      fun 𝓕 => ∀ s ∈ 𝓕, ∀ t ∈ 𝓕, s ∪ t ∈ 𝓕
    let EmptyFree : Finset (Finset Vertex) → Prop := fun 𝓕 => ∅ ∉ 𝓕
    let EmptyTotalIntersection : Finset (Finset Vertex) → Prop :=
      fun 𝓕 => ∀ x : Vertex, ∃ s ∈ 𝓕, x ∉ s
    let Shares : Vertex → Finset (Finset Vertex) → Finset (Finset Vertex) → Prop :=
      fun x 𝓕 𝓖 => (∃ s ∈ 𝓕, x ∈ s) ∧ ∃ t ∈ 𝓖, x ∈ t
    let PairwiseUnionsDistinct : Prop :=
      ∀ s₁ ∈ familyA, ∀ t₁ ∈ familyB, ∀ s₂ ∈ familyA, ∀ t₂ ∈ familyB,
        s₁ ∪ t₁ = s₂ ∪ t₂ → s₁ = s₂ ∧ t₁ = t₂
    let pairwiseUnionPairs : Finset (Finset Vertex) :=
      (familyA.product familyB).image (fun p => p.1 ∪ p.2)
    UnionClosed familyA ∧
      UnionClosed familyB ∧
      EmptyFree familyA ∧
      EmptyFree familyB ∧
      EmptyTotalIntersection familyA ∧
      EmptyTotalIntersection familyB ∧
      Shares z familyA familyB ∧
      PairwiseUnionsDistinct ∧
      pairwiseUnionPairs.card = 9 ∧
      (pairwiseUnionPairs.filter (fun s => z ∈ s)).card = 8 := by
  dsimp
  decide

end MathlibPlus.Combinatorics.CommonCoreOverlap
