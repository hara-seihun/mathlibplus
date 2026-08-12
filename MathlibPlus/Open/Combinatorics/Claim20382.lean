import MathlibPlus.Open.Basic

namespace MathlibPlus.Open.Combinatorics

/-!
Formalization of admitted claim 20382.  The ground set is the union of the
members actually occurring in the finite family; no ambient finite universe is
added.  "At least half" is expressed by the exact integer comparison
`2 * count ≥ F.card`.
-/

/-- Frankl's conjecture for ordinary finite union-closed families on at most
 twelve actual ground elements. -/
def franklConjectureGroundCardAtMost12_claim20382 : Prop :=
  ∀ {α : Type*} [DecidableEq α],
    ∀ F : Finset (Finset α),
      F.Nonempty →
      (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
      (F.biUnion (fun A => A)).card ≤ 12 →
      ∃ x ∈ F.biUnion (fun A => A),
        2 * (F.filter (fun A => x ∈ A)).card ≥ F.card

end MathlibPlus.Open.Combinatorics
