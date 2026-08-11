import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Dense-link reduction from a constant-spread three-disjoint-members lemma to
three-sunflower existence.  The source's `R`-spread convention is made explicit
here as the displayed trace-cardinality inequality. -/
def denseLinkThreeSunflower : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α] (R : ℝ),
    1 < R →
    (∀ (w : ℕ) (G : Finset (Finset α)),
      (∀ A ∈ G, A.card = w) →
      (∀ T : Finset α, T.Nonempty →
        ((G.filter (fun A => T ⊆ A)).card : ℝ) ≤
          (G.card : ℝ) / R ^ T.card) →
      (G.card : ℝ) > R ^ w →
      ∃ A B C : Finset α,
        A ∈ G ∧ B ∈ G ∧ C ∈ G ∧
        A ∩ B = ∅ ∧ A ∩ C = ∅ ∧ B ∩ C = ∅) →
    ∀ (F : Finset (Finset α)) (n : ℕ),
      (∀ A ∈ F, A.card = n) →
      (F.card : ℝ) > R ^ n →
      ∃ A B C : Finset α,
        A ∈ F ∧ B ∈ F ∧ C ∈ F ∧
        A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
        A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C

end MathlibPlus.Open.Combinatorics
