import Mathlib

namespace MathlibPlus.Open.Combinatorics.R3183Claim47031

private def familyGround {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Finset α :=
  𝓕.biUnion (fun A => A)

private def occurrenceCount {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (x : α) : ℕ :=
  (𝓕.filter (fun A => x ∈ A)).card

private def unionClosedFamily {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ∪ B ∈ 𝓕

private def minimalNonemptyMembers {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Finset (Finset α) :=
  𝓕.filter (fun M =>
    M.Nonempty ∧
      ∀ ⦃N : Finset α⦄, N ∈ 𝓕 → N.Nonempty → N ⊆ M → M ⊆ N)

private def franklConclusion {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∃ c ∈ familyGround 𝓕,
    2 * occurrenceCount 𝓕 c ≥ 𝓕.card

private def franklCounterexample {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  𝓕.Nonempty ∧
    (familyGround 𝓕).Nonempty ∧
    unionClosedFamily 𝓕 ∧
    ∀ c ∈ familyGround 𝓕,
      2 * occurrenceCount 𝓕 c < 𝓕.card

private def noTwoCoordinateTransversal {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ x ∈ familyGround 𝓕, ∀ y ∈ familyGround 𝓕,
    ∃ M ∈ minimalNonemptyMembers 𝓕, x ∉ M ∧ y ∉ M

private def minimalMemberTransversalAtLeastThree
    {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∀ T : Finset α, T ⊆ familyGround 𝓕 → T.card ≤ 2 →
    ∃ M ∈ minimalNonemptyMembers 𝓕, Disjoint T M

/-- Claim 47031: a finite union-closed Frankl counterexample has no
transversal of its actual minimal-member hypergraph of size at most two, and
an ordinary nontrivial union-closed family with at most two such members
satisfies the half-incidence conclusion. -/
def unionClosedFranklCounterexampleNoTwoTransversal_claim47031 : Prop :=
  (∀ {α : Type*} [DecidableEq α]
      (𝓕 : Finset (Finset α)),
      franklCounterexample 𝓕 →
        noTwoCoordinateTransversal 𝓕 ∧
          minimalMemberTransversalAtLeastThree 𝓕) ∧
    (∀ {α : Type*} [DecidableEq α]
      (𝓕 : Finset (Finset α)),
      𝓕.Nonempty →
      (familyGround 𝓕).Nonempty →
      unionClosedFamily 𝓕 →
      (minimalNonemptyMembers 𝓕).card ≤ 2 →
        franklConclusion 𝓕)

end MathlibPlus.Open.Combinatorics.R3183Claim47031
