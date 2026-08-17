import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.HypermatchingSwapFactorization

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

def characteristicProduct {R : Type*} [CommRing R] {e : ℕ}
    (occurrences : Fin (2 * e) → R) (A : Finset (Fin (2 * e))) : Polynomial R :=
  ∏ i ∈ A, (Polynomial.X + Polynomial.C (occurrences i))

def hypermatchingLinearState {R : Type*} [CommRing R] {e : ℕ}
    (occurrences : Fin (2 * e) → R) (E : Finset (Fin (2 * e))) : Polynomial R :=
  characteristicProduct occurrences E +
    characteristicProduct occurrences (complementWithin e E)

/-- The complementary swap decomposition factors the difference of the two
    degree-two hypermatching states into two lower-arity product differences. -/
def claim24770 : Prop :=
  ∀ {R : Type*} [CommRing R] (e : ℕ)
    (occurrences : Fin (2 * e) → R)
    (E F A B C D : Finset (Fin (2 * e))) (r : ℕ),
    complementarySwapDecomposition e E F A B C D r →
    hypermatchingLinearState occurrences E - hypermatchingLinearState occurrences F =
        (characteristicProduct occurrences A - characteristicProduct occurrences B) *
          (characteristicProduct occurrences C - characteristicProduct occurrences D) ∧
      A.card < e ∧ B.card < e ∧ C.card < e ∧ D.card < e

end MathlibPlus.Open.ResearchFormalization.Batch_38f4415f.HypermatchingSwapFactorization
