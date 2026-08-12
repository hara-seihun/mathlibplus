import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-!
The informal claim calls a family "nontrivial" without defining that word.
This registry node makes the convention explicit: the family is nonempty and
is not the singleton family containing only the empty set.  It is represented
as a finite set of finite subsets of a finite ground type.
-/

/-- Every finite nontrivial union-closed family has an element in at least
`(3 - √5) / 2` of its members. -/
def universalAbundanceConstant : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α]
    (𝓕 : Finset (Finset α)),
    𝓕.Nonempty →
    𝓕 ≠ {∅} →
    (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕) →
    ∃ x : α,
      ((𝓕.filter (fun A => x ∈ A)).card : ℝ) ≥
        ((3 - Real.sqrt 5) / 2) * (𝓕.card : ℝ)

end MathlibPlus.Open.Combinatorics
