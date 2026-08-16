import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

/-- The explicit eight-vertex graph `C`, written as a symmetric directed
edge relation so that the induced cards have a finite exact carrier. -/
def C : Finset (Fin 9 × Fin 9) :=
  {((0 : Fin 9), 3), (3, 0),
   (0, 4), (4, 0),
   (0, 7), (7, 0),
   (1, 4), (4, 1),
   (1, 5), (5, 1),
   (1, 6), (6, 1),
   (2, 5), (5, 2),
   (2, 6), (6, 2),
   (2, 7), (7, 2),
   (3, 6), (6, 3),
   (3, 7), (7, 3),
   (5, 7), (7, 5)}

/-- The two leaf extensions at vertices `3` and `5`, respectively. -/
def G₃ : Finset (Fin 9 × Fin 9) :=
  C ∪ {((8 : Fin 9), 3), (3, 8)}

def G₅ : Finset (Fin 9 × Fin 9) :=
  C ∪ {((8 : Fin 9), 5), (5, 8)}

/-- Relabel the induced graph on the eight vertices other than `v`. -/
def deletedCard (edges : Finset (Fin 9 × Fin 9)) (v : Fin 9) :
    Finset (Fin 8 × Fin 8) :=
  (Finset.univ : Finset (Fin 8 × Fin 8)).filter fun p =>
    (Fin.succAbove v p.1, Fin.succAbove v p.2) ∈ edges

/-- The full vertex-deleted deck, with multiplicity. -/
def deck (edges : Finset (Fin 9 × Fin 9)) :
    Multiset (Finset (Fin 8 × Fin 8)) :=
  (Finset.univ : Finset (Fin 9)).val.map (deletedCard edges)

/-- An adjacency relation on `Fin 8` is encoded injectively by its binary edge
mask. -/
def relationCode (A : Finset (Fin 8 × Fin 8)) : Nat :=
  ∑ p ∈ A, 2 ^ (8 * p.1.val + p.2.val)

/-- The orbit of the exact adjacency mask under all vertex permutations. -/
def graphKey (A : Finset (Fin 8 × Fin 8)) : Finset Nat :=
  (Finset.univ : Finset (Equiv.Perm (Fin 8))).image fun e =>
    relationCode
      ((Finset.univ : Finset (Fin 8 × Fin 8)).filter fun p =>
        (e.symm p.1, e.symm p.2) ∈ A)

/-- Exact graph isomorphism for the finite card carrier. -/
def graphIso (A B : Finset (Fin 8 × Fin 8)) : Prop :=
  graphKey A = graphKey B

/-- The multiset intersection of two decks after quotienting cards by exact
isomorphism, so repeated isomorphism classes retain their multiplicity. -/
def isoDeckIntersection :
    Multiset (Finset (Fin 8 × Fin 8)) →
      Multiset (Finset (Fin 8 × Fin 8)) → Multiset (Finset Nat) :=
  fun A B => Multiset.inter (A.map graphKey) (B.map graphKey)

/-- The multiset intersection of the full vertex-deleted decks of `G₃` and
`G₅`, using exact graph isomorphism and retaining multiplicity, has cardinality
exactly `3`. -/
def claim13989 : Prop :=
  (isoDeckIntersection (deck G₃) (deck G₅)).card = 3

end MathlibPlus.Open.ResearchFormalization
