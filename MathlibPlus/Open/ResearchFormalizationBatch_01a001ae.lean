import Mathlib

namespace MathlibPlus.Open.CellularZeroPacking

noncomputable section

/-- A point in the open real cell indexed by an integer. -/
def inCell (n : ℤ) (x : ℝ) : Prop :=
  (n : ℝ) < x ∧ x < ((n + 1 : ℤ) : ℝ)

/-- There are `m` zeros in strictly increasing cells, with one point chosen in
    each cell.  The indexing by `Fin m` records the strict order and therefore
    discards multiplicities and additional zeros in a cell. -/
def hasCellularZeroPacking (F : ℝ → ℝ) (m : ℕ) : Prop :=
  ∃ n : Fin m → ℤ,
    StrictMono n ∧
      ∃ x : Fin m → ℝ,
        ∀ i, inCell (n i) (x i) ∧ F (x i) = 0

/-- The supremum, in the extended natural numbers, of the admissible packing
    sizes. -/
def cellularZeroPacking (F : ℝ → ℝ) : ℕ∞ :=
  sSup {m : ℕ∞ | ∃ k : ℕ, m = (k : ℕ∞) ∧ hasCellularZeroPacking F k}

/-- The function obtained from a selected subflag by a coefficient vector. -/
def fiberLinearCombination {r : ℕ} (f : ℕ → ℝ → ℝ)
    (j : Fin r → ℕ) (c : Fin r → ℝ) : ℝ → ℝ :=
  fun x => ∑ k, c k * f (j k) x

/-- Strict positivity of all evaluation determinants on increasing cellular
    transversals for all strictly selected subflags. -/
def strictCellularChebyshev (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ r : ℕ, ∀ j : Fin r → ℕ, StrictMono j →
    ∀ n : Fin r → ℤ, StrictMono n →
      ∀ x : Fin r → ℝ, (∀ i, inCell (n i) (x i)) →
        0 < Matrix.det (fun i k => f (j k) (x i))

/-- Cellular zero-packing duality: strict cellular Chebyshev positivity for
    every rank subflag is equivalent to the sharp zero-packing bound for every
    nonzero real linear combination of its fibers. -/
def cellularZeroPackingDuality (f : ℕ → ℝ → ℝ) : Prop :=
  strictCellularChebyshev f ↔
    ∀ r : ℕ, ∀ j : Fin r → ℕ, StrictMono j →
      ∀ c : Fin r → ℝ, (∃ k, c k ≠ 0) →
        cellularZeroPacking (fiberLinearCombination f j c) ≤ (r - 1 : ℕ∞)

end
end MathlibPlus.Open.CellularZeroPacking


namespace MathlibPlus.Open.CayleyDih

noncomputable section

instance subtypeFintype {α : Type} [Fintype α] (p : α → Prop) :
    Fintype {a : α // p a} := Fintype.ofFinite _

/-- The underlying set of `F_3^2 ⋊ C_2`; the operations below use the
    nontrivial element of `C_2` for the negation action. -/
abbrev R := (ZMod 3 × ZMod 3) × ZMod 2

def negateBy (a : ZMod 2) (z : ZMod 3) : ZMod 3 :=
  if a = 0 then z else -z

def rMul (x y : R) : R :=
  ((x.1.1 + negateBy x.2 y.1.1,
      x.1.2 + negateBy x.2 y.1.2), x.2 + y.2)

def rOne : R := ((0, 0), 0)

def rInv (x : R) : R :=
  ((if x.2 = 0 then -x.1.1 else x.1.1,
      if x.2 = 0 then -x.1.2 else x.1.2), -x.2)

/-- A connection set is inverse-closed and excludes the identity. -/
def inverseClosedConnectionSet (S : Finset R) : Prop :=
  (∀ s ∈ S, s ≠ rOne) ∧ ∀ s ∈ S, rInv s ∈ S

/-- The undirected Cayley graph obtained from a connection set by right
    multiplication.  `SimpleGraph.fromRel` symmetrizes the displayed edge
    relation and removes loops. -/
def cayley (S : Finset R) : SimpleGraph R :=
  SimpleGraph.fromRel (fun x y => ∃ s ∈ S, y = rMul x s)

def block (n : ℕ) (v : Fin 18) : ℕ := v.val / n

def localCoord (n : ℕ) (v : Fin 18) : ℕ := v.val % n

def sameBlock (n : ℕ) (u v : Fin 18) : Prop := block n u = block n v

def cycleAdjacent (n a b : ℕ) : Prop :=
  (a + 1) % n = b % n ∨ (b + 1) % n = a % n

/-- Explicit representatives on `Fin 18` of the eleven graph forms in the
    admitted table.  Blocks are consecutive components; the local coordinates
    give the indicated cycles, complete multipartite graphs, or Cartesian
    products. -/
def classRel (i : Fin 11) (u v : Fin 18) : Prop :=
  match i.val with
  | 0 => False
  | 1 => sameBlock 2 u v ∧ localCoord 2 u ≠ localCoord 2 v
  | 2 => sameBlock 3 u v ∧ localCoord 3 u ≠ localCoord 3 v
  | 3 => sameBlock 6 u v ∧ cycleAdjacent 6 (localCoord 6 u) (localCoord 6 v)
  | 4 =>
      sameBlock 6 u v ∧
        ((localCoord 6 u / 3 = localCoord 6 v / 3 ∧
            cycleAdjacent 3 (localCoord 6 u) (localCoord 6 v)) ∨
          (localCoord 6 u % 3 = localCoord 6 v % 3 ∧
            localCoord 6 u / 3 ≠ localCoord 6 v / 3))
  | 5 =>
      sameBlock 6 u v ∧
        ((localCoord 6 u < 3 ∧ 3 ≤ localCoord 6 v) ∨
          (localCoord 6 v < 3 ∧ 3 ≤ localCoord 6 u))
  | 6 =>
      sameBlock 9 u v ∧ localCoord 9 u ≠ localCoord 9 v ∧
        (localCoord 9 u / 3 = localCoord 9 v / 3 ∨ localCoord 9 u % 3 = localCoord 9 v % 3)
  | 7 =>
      sameBlock 6 u v ∧ localCoord 6 u ≠ localCoord 6 v ∧
        localCoord 6 u % 3 ≠ localCoord 6 v % 3
  | 8 => sameBlock 6 u v ∧ localCoord 6 u ≠ localCoord 6 v
  | 9 => sameBlock 9 u v ∧ localCoord 9 u / 3 ≠ localCoord 9 v / 3
  | _ => sameBlock 9 u v ∧ localCoord 9 u ≠ localCoord 9 v

def classGraph (i : Fin 11) : SimpleGraph (Fin 18) :=
  SimpleGraph.fromRel (classRel i)

def classValency (i : Fin 11) : ℕ :=
  match i.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 3
  | 5 => 3
  | 6 => 4
  | 7 => 4
  | 8 => 5
  | 9 => 6
  | _ => 8

def classFiberCount (i : Fin 11) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 9
  | 2 => 4
  | 3 => 36
  | 4 => 36
  | 5 => 12
  | 6 => 6
  | 7 => 36
  | 8 => 12
  | 9 => 4
  | _ => 1

def graphIsoToClass (S : Finset R) (i : Fin 11) : Prop :=
  Nonempty (cayley S ≃g classGraph i)

/-- The exact finite enumeration and the eleven unlabeled graph classes from
    the admitted `F_3^2 ⋊ C_2` disconnected-Cayley-graph claim. -/
def disconnectedCayleyEnumeration : Prop :=
  Fintype.card {S : Finset R // inverseClosedConnectionSet S} = 8192 ∧
    Fintype.card {S : Finset R //
      inverseClosedConnectionSet S ∧ ¬(cayley S).Connected} = 157 ∧
    (∀ i : Fin 11, ∀ v : Fin 18,
      Fintype.card {w : Fin 18 // (classGraph i).Adj v w} = classValency i) ∧
    (∀ i j : Fin 11, i ≠ j → ¬ Nonempty (classGraph i ≃g classGraph j)) ∧
    (∀ S : Finset R,
      inverseClosedConnectionSet S → ¬(cayley S).Connected →
        ∃! i : Fin 11, graphIsoToClass S i) ∧
    (∀ i : Fin 11,
      Fintype.card {S : Finset R //
        inverseClosedConnectionSet S ∧ ¬(cayley S).Connected ∧
          graphIsoToClass S i} = classFiberCount i)

end
end MathlibPlus.Open.CayleyDih
