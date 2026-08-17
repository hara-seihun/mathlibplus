import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.ComplementarySwapDecomposition

open scoped BigOperators

def complementWithin (e : ℕ) (E : Finset (Fin (2 * e))) : Finset (Fin (2 * e)) :=
  Finset.univ \ E

def fourPartsPairwiseDisjoint {e : ℕ}
    (A B C D : Finset (Fin (2 * e))) : Prop :=
  Disjoint A B ∧ Disjoint A C ∧ Disjoint A D ∧
    Disjoint B C ∧ Disjoint B D ∧ Disjoint C D

def complementarySwapDecomposition (e : ℕ)
    (E F A B C D : Finset (Fin (2 * e))) (r : ℕ) : Prop :=
  E.card = e ∧ F.card = e ∧
    E = A ∪ C ∧ complementWithin e E = B ∪ D ∧
    F = A ∪ D ∧ complementWithin e F = B ∪ C ∧
    fourPartsPairwiseDisjoint A B C D ∧
    A.card = r ∧ B.card = r ∧
    C.card = e - r ∧ D.card = e - r ∧
    1 ≤ r ∧ r ≤ e - 1

/-- Two distinct unordered balanced bipartitions of one common occurrence
    universe admit the complementary swap decomposition. -/
def claim24769 : Prop :=
  ∀ (e : ℕ) (E F : Finset (Fin (2 * e))),
    E.card = e → F.card = e →
    E ≠ F → F ≠ complementWithin e E →
    ∃ (A B C D : Finset (Fin (2 * e))) (r : ℕ),
      complementarySwapDecomposition e E F A B C D r

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.ComplementarySwapDecomposition
