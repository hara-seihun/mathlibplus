import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2939TwoTriangles

noncomputable section

/-- Claim 45293: the literal six-edge family of two disjoint triangles is a
3-sunflower-free ordinary 2-uniform family, with the exact two cases for
triple intersections. -/
def exactTwoTriangleSunflowerFree_claim45293 : Prop :=
  let F : Finset (Finset (Fin 6)) :=
    {{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5}}
  let L : Finset (Fin 6) := {0, 1, 2}
  let R : Finset (Fin 6) := {3, 4, 5}
  F.card = 6 ∧
    (∀ A ∈ F, A.card = 2) ∧
    (∀ A B C : Finset (Fin 6),
      A ∈ F → B ∈ F → C ∈ F →
      A ≠ B → A ≠ C → B ≠ C →
      ((A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C) → False)) ∧
    (∀ A B C : Finset (Fin 6),
      A ∈ F → B ∈ F → C ∈ F →
      A ≠ B → A ≠ C → B ≠ C →
      ((A ∪ B ∪ C ⊆ L) →
        (A ∩ B).card = 1 ∧ (A ∩ C).card = 1 ∧
          (B ∩ C).card = 1 ∧ A ∩ B ≠ A ∩ C ∧
          A ∩ B ≠ B ∩ C ∧ A ∩ C ≠ B ∩ C) ∧
      ((A ∪ B ∪ C ⊆ R) →
        (A ∩ B).card = 1 ∧ (A ∩ C).card = 1 ∧
          (B ∩ C).card = 1 ∧ A ∩ B ≠ A ∩ C ∧
          A ∩ B ≠ B ∩ C ∧ A ∩ C ≠ B ∩ C) ∧
      ¬(A ∪ B ∪ C ⊆ L) → ¬(A ∪ B ∪ C ⊆ R) →
        ((A ∩ B).card = 1 ∧ A ∩ C = ∅ ∧ B ∩ C = ∅) ∨
        ((A ∩ C).card = 1 ∧ A ∩ B = ∅ ∧ B ∩ C = ∅) ∨
        ((B ∩ C).card = 1 ∧ A ∩ B = ∅ ∧ A ∩ C = ∅))

end

end MathlibPlus.Open.ResearchFormalization.R2939TwoTriangles
