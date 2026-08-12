import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-!
Formalization of claim 16526.  A `Finset (Finset α)` represents a finite
family of distinct finite sets.  The separate finite set `U` is required to
be exactly the union of the family, so it is the actual ground set rather than
an ambient superset.  Union-closure quantifies over every pair of members.
-/

def ordinaryFiniteUnionClosedFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (U : Finset α) : Prop :=
  (∀ A ∈ F, A ⊆ U) ∧
    (∀ x ∈ U, ∃ A, A ∈ F ∧ x ∈ A) ∧
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F)

end MathlibPlus.Combinatorics
