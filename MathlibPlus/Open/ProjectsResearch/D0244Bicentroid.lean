import Mathlib

namespace MathlibPlus.Open.ProjectsResearch.D0244

/-- A bicentroid tree is represented by its finite simple graph, whose center
is exactly the two endpoints of a central edge. -/
def bicentroidTree {h : ℕ} (T : SimpleGraph (Fin (2 * h)))
    (a b : Fin (2 * h)) : Prop :=
  T.IsTree ∧ T.center = ({a, b} : Set (Fin (2 * h))) ∧ T.Adj a b

/-- The two rooted halves produced by deleting the central edge. -/
def rootedHalfSplit {h : ℕ} (T : SimpleGraph (Fin (2 * h)))
    (a b : Fin (2 * h)) (A B : Set (Fin (2 * h))) : Prop :=
  A ∩ B = ∅ ∧ A ∪ B = Set.univ ∧
    a ∈ A ∧ b ∈ B ∧ Nat.card A = h ∧ Nat.card B = h ∧
    (T.induce A).Connected ∧ (T.induce B).Connected ∧
    (∀ x ∈ A, ∀ y ∈ B, T.Adj x y ↔ x = a ∧ y = b)

/-- Claim 6766. -/
def bicentroidTreeHasEqualRootedHalves : Prop :=
  ∀ (h : ℕ) (T : SimpleGraph (Fin (2 * h)))
    (a b : Fin (2 * h)),
    bicentroidTree T a b →
      ∃ A B : Set (Fin (2 * h)), rootedHalfSplit T a b A B

/-- A connected carrier of the equatorial size. -/
def equatorialCarrier {h : ℕ} (T : SimpleGraph (Fin (2 * h)))
    (C : Set (Fin (2 * h))) : Prop :=
  C.Nonempty ∧ Nat.card C = h ∧ (T.induce C).Connected

/-- Claim 6767: after the central-edge split, every connected carrier of half
size is exactly one of the two central-containing cases or one rooted half. -/
def equatorialCarrierTrichotomy : Prop :=
  ∀ (h : ℕ) (T : SimpleGraph (Fin (2 * h)))
    (a b : Fin (2 * h)) (A B : Set (Fin (2 * h))),
    bicentroidTree T a b → rootedHalfSplit T a b A B →
    ∀ C : Set (Fin (2 * h)), equatorialCarrier T C →
      (({a, b} : Set (Fin (2 * h))) ⊆ C ∧ C ≠ A ∧ C ≠ B) ∨
      (C = A ∧ ¬ (({a, b} : Set (Fin (2 * h))) ⊆ C) ∧ C ≠ B) ∨
      (C = B ∧ ¬ (({a, b} : Set (Fin (2 * h))) ⊆ C) ∧ C ≠ A)

end MathlibPlus.Open.ProjectsResearch.D0244
