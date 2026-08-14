import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The number of edges leaving a finite vertex set. -/
def boundarySize {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact ∑ x ∈ S, (Finset.univ.filter (fun y => T.Adj x y ∧ y ∉ S)).card

def connectedSet {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ (T.induce (S : Set V)).Connected

def componentSet {V : Type} (G : SimpleGraph V) (x : V) : Set V :=
  {y | G.Reachable x y}

def componentSets {V : Type} [Fintype V] (G : SimpleGraph V) : Finset (Set V) := by
  classical
  exact Finset.univ.image (componentSet G)

def componentCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ :=
  (componentSets G).card

def deleteVertices {V : Type} [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) : SimpleGraph {v // v ∉ S} :=
  T.induce {v | v ∉ S}

def deletedComponentCount {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (S : Finset V) (x : V) : ℕ :=
  componentCount (deleteVertices T (S ∪ {x}))

def degreeCount {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (x : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun y => T.Adj x y)).card

def adjacentToSet {V : Type} [DecidableEq V]
    (T : SimpleGraph V) (x : V) (S : Finset V) : Prop :=
  ∃ y, y ∈ S ∧ T.Adj x y

def connectedSubtreePolynomial {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : MvPolynomial (Fin 2) ℤ := by
  classical
  exact ∑ S ∈ (Finset.univ.powerset.filter (connectedSet T)),
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ S.card *
      (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) ^ boundarySize T S

/-- Claim 22247: the displayed boundary-refined connected-subtree polynomial. -/
def claim22247 : Prop := by
  classical
  exact ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V),
    T.IsTree →
      connectedSubtreePolynomial T =
        ∑ S ∈ (Finset.univ.powerset.filter (connectedSet T)),
          (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ^ S.card *
            (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ) ^ boundarySize T S

def oneHoleCount {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (m k : ℕ) : ℕ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset V).powerset,
    ∑ x ∈ (Finset.univ : Finset V),
      if x ∉ S ∧ connectedSet T S ∧ S.card = m ∧ deletedComponentCount T S x = k
      then 1 else 0

def oneHoleTransform {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : MvPolynomial (Fin 2) ℕ := by
  classical
  exact ∑ m ∈ Finset.range (Fintype.card V + 1),
    ∑ k ∈ Finset.range (Fintype.card V + 1),
      MvPolynomial.C (oneHoleCount T m k) *
        (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) ^ m *
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℕ) ^ k

/-- Claim 22254: the one-hole counts and their generating transform. -/
def claim22254 : Prop := by
  classical
  exact ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V),
    T.IsTree →
      oneHoleTransform T =
        ∑ m ∈ Finset.range (Fintype.card V + 1),
          ∑ k ∈ Finset.range (Fintype.card V + 1),
            MvPolynomial.C (oneHoleCount T m k) *
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℕ) ^ m *
              (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℕ) ^ k

/-- Claim 22256: deletion component count at a connected set and an outside vertex. -/
def claim22256 : Prop := by
  classical
  exact ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V),
    T.IsTree →
      ∀ (S : Finset V) (x : V),
        (T.induce (S : Set V)).Connected → x ∉ S →
          deletedComponentCount T S x =
            boundarySize T S - 1 + degreeCount T x -
              (if adjacentToSet T x S then 1 else 0)

def coeffLaurent (p : Polynomial ℤ) : LaurentPolynomial (Polynomial ℤ) :=
  LaurentPolynomial.C p

def zPower (n : ℕ) : LaurentPolynomial (Polynomial ℤ) :=
  LaurentPolynomial.T (n : ℤ)

def connectedSubtreeLaurent {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : LaurentPolynomial (Polynomial ℤ) := by
  classical
  exact ∑ S ∈ (Finset.univ.powerset.filter (connectedSet T)),
    coeffLaurent (Polynomial.X ^ S.card) * zPower (boundarySize T S)

def degreeLaurent {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : LaurentPolynomial (Polynomial ℤ) := by
  classical
  exact ∑ x ∈ (Finset.univ : Finset V), zPower (degreeCount T x)

def markedInsideLaurent {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : LaurentPolynomial (Polynomial ℤ) := by
  classical
  exact ∑ S ∈ (Finset.univ.powerset.filter (connectedSet T)),
    coeffLaurent (Polynomial.X ^ S.card) * zPower (boundarySize T S) *
      (∑ x ∈ S, zPower (degreeCount T x))

def markedBoundaryLaurent {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : LaurentPolynomial (Polynomial ℤ) := by
  classical
  exact ∑ S ∈ (Finset.univ.powerset.filter (connectedSet T)),
    coeffLaurent (Polynomial.X ^ S.card) * zPower (boundarySize T S) *
      (∑ x ∈ (Finset.univ.filter (fun x => x ∉ S ∧ adjacentToSet T x S)),
        zPower (degreeCount T x))

def oneHoleTransformLaurent {V : Type} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) : LaurentPolynomial (Polynomial ℤ) := by
  classical
  exact ∑ m ∈ Finset.range (Fintype.card V + 1),
    ∑ k ∈ Finset.range (Fintype.card V + 1),
      coeffLaurent (Polynomial.C (oneHoleCount T m k : ℤ) * Polynomial.X ^ m) * zPower k

def zMinusOne : LaurentPolynomial (Polynomial ℤ) := LaurentPolynomial.T (-1)
def zMinusTwo : LaurentPolynomial (Polynomial ℤ) := LaurentPolynomial.T (-2)

/-- Claim 22257: the exact Laurent-polynomial boundary/degree interface. -/
def claim22257 : Prop := by
  classical
  exact ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V),
    T.IsTree →
      oneHoleTransformLaurent T =
        zMinusOne * (degreeLaurent T * connectedSubtreeLaurent T -
          markedInsideLaurent T) +
          (zMinusTwo - zMinusOne) * markedBoundaryLaurent T

def forestComponentWeight (s : ℕ) : MvPolynomial (Fin 4) ℤ :=
  if s = 1 then MvPolynomial.X 0 else
    1 + (MvPolynomial.X 1 : MvPolynomial (Fin 4) ℤ) * (MvPolynomial.X 2) ^ (s - 1)

def forestSignedCutPolynomial {V : Type} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) : MvPolynomial (Fin 4) ℤ := by
  classical
  exact ∑ C ∈ F.edgeFinset.powerset,
    (-1 : MvPolynomial (Fin 4) ℤ) ^ (F.edgeFinset.card - C.card) *
      (MvPolynomial.X 3 : MvPolynomial (Fin 4) ℤ) ^ C.card *
      (∏ K ∈ componentSets (F.deleteEdges (C : Set (Sym2 V))),
        forestComponentWeight K.ncard)

/-- Claim 22218: the singleton-refined signed cut polynomial of a forest. -/
def claim22218 : Prop := by
  classical
  exact ∀ {V : Type} [Fintype V] [DecidableEq V] (F : SimpleGraph V),
    F.IsAcyclic →
      forestComponentWeight 1 = (MvPolynomial.X 0 : MvPolynomial (Fin 4) ℤ) ∧
      (∀ s : ℕ, 2 ≤ s →
        forestComponentWeight s =
          1 + (MvPolynomial.X 1 : MvPolynomial (Fin 4) ℤ) * (MvPolynomial.X 2) ^ (s - 1)) ∧
      forestSignedCutPolynomial F =
        ∑ C ∈ F.edgeFinset.powerset,
          (-1 : MvPolynomial (Fin 4) ℤ) ^ (F.edgeFinset.card - C.card) *
            (MvPolynomial.X 3 : MvPolynomial (Fin 4) ℤ) ^ C.card *
            (∏ K ∈ componentSets (F.deleteEdges (C : Set (Sym2 V))),
              forestComponentWeight K.ncard)

end MathlibPlus.Open.ResearchFormalizationBatch
