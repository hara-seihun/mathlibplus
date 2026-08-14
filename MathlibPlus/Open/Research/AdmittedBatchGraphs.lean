import Mathlib

namespace MathlibPlus.Open.Research.AdmittedBatchGraphs

private def leftEdgeCode (a b : Fin 11) : Prop :=
  (a.val = 0 ∧ b.val = 1) ∨
  (a.val = 0 ∧ b.val = 7) ∨
  (a.val = 1 ∧ b.val = 2) ∨
  (a.val = 1 ∧ b.val = 5) ∨
  (a.val = 1 ∧ b.val = 6) ∨
  (a.val = 2 ∧ b.val = 3) ∨
  (a.val = 2 ∧ b.val = 4) ∨
  (a.val = 7 ∧ b.val = 8) ∨
  (a.val = 7 ∧ b.val = 10) ∨
  (a.val = 8 ∧ b.val = 9)

private def rightEdgeCode (a b : Fin 11) : Prop :=
  (a.val = 0 ∧ b.val = 1) ∨
  (a.val = 0 ∧ b.val = 5) ∨
  (a.val = 0 ∧ b.val = 10) ∨
  (a.val = 1 ∧ b.val = 2) ∨
  (a.val = 2 ∧ b.val = 3) ∨
  (a.val = 2 ∧ b.val = 4) ∨
  (a.val = 5 ∧ b.val = 6) ∨
  (a.val = 5 ∧ b.val = 8) ∨
  (a.val = 5 ∧ b.val = 9) ∨
  (a.val = 6 ∧ b.val = 7)

def leftBaseTree : SimpleGraph (Fin 11) := SimpleGraph.fromRel leftEdgeCode

def rightBaseTree : SimpleGraph (Fin 11) := SimpleGraph.fromRel rightEdgeCode

def claim42469 : Prop :=
  leftBaseTree.IsTree ∧
    rightBaseTree.IsTree ∧
    ¬ Nonempty (SimpleGraph.Iso leftBaseTree rightBaseTree)

private def fanEdgeCode {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) (k : ℕ)
    (x y : Fin (n + k)) : Prop :=
  (∃ a b : Fin n,
      x = Fin.castAdd k a ∧ y = Fin.castAdd k b ∧ T.Adj a b) ∨
  (∃ j : Fin k,
      x = Fin.castAdd k v ∧ y = Fin.natAdd n j)

def fan {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) (k : ℕ) :
    SimpleGraph (Fin (n + k)) :=
  SimpleGraph.fromRel (fanEdgeCode T v k)

private def fanCanonicalAdjacency {n : ℕ} (T : SimpleGraph (Fin n)) (v : Fin n) (k : ℕ)
    (x y : Fin (n + k)) : Prop :=
  x ≠ y ∧ (fanEdgeCode T v k x y ∨ fanEdgeCode T v k y x)

def claim42472 : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (v : Fin n) (k : ℕ),
    T.IsTree →
      ∀ (x y : Fin (n + k)),
        (fan T v k).Adj x y ↔ fanCanonicalAdjacency T v k x y

end MathlibPlus.Open.Research.AdmittedBatchGraphs
