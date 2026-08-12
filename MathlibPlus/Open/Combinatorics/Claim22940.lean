import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The admitted three-disjoint-triple minima theorem.  The finite family is
represented by a `Finset` of finite subsets of an arbitrary coordinate universe,
so distinctness is built in and coordinates outside the nine distinguished
points remain available.  No assumption about whether the empty set belongs
to the family is added. -/
def threeDisjointTripleMinima_claim22940 : Prop :=
  ∀ (V : Type*) [DecidableEq V]
    (F : Finset (Finset V)) (M₁ M₂ M₃ : Finset V),
    M₁ ∈ F ∧ M₂ ∈ F ∧ M₃ ∈ F ∧
      M₁.card = 3 ∧ M₂.card = 3 ∧ M₃.card = 3 ∧
      (∀ x, x ∈ M₁ → x ∉ M₂) ∧
      (∀ x, x ∈ M₁ → x ∉ M₃) ∧
      (∀ x, x ∈ M₂ → x ∉ M₃) ∧
      (∀ A, A ∈ F → ∀ B, B ∈ F → A ∪ B ∈ F) ∧
      (∀ A, A ∈ F → A.Nonempty →
        ((∀ B, B ∈ F → B.Nonempty → B ⊆ A → A ⊆ B) ↔
          A = M₁ ∨ A = M₂ ∨ A = M₃)) →
    ∃ x, x ∈ M₁ ∪ M₂ ∪ M₃ ∧
      2 * (F.filter (fun A => x ∈ A)).card ≥ F.card

end MathlibPlus.Open.Combinatorics
