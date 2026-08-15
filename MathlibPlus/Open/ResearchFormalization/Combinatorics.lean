import Mathlib

noncomputable section

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev CubeVertex (n : ℕ) := Fin n → ZMod 2

def cubeUnit (n : ℕ) (i : Fin n) : CubeVertex n :=
  fun j => if j = i then 1 else 0

def cutBoundaryEdge {n : ℕ} (g : CubeVertex n → Bool)
    (x : CubeVertex n) (i : Fin n) : Prop :=
  x i = 0 ∧ g x ≠ g (x + cubeUnit n i)

def cutBoundaryEdgeSet {n : ℕ} (g : CubeVertex n → Bool) :
    Finset (CubeVertex n × Fin n) :=
  Finset.univ.filter (fun e => cutBoundaryEdge g e.1 e.2)

def cutBoundaryAdj {n : ℕ} (g : CubeVertex n → Bool)
    (x y : CubeVertex n) : Prop :=
  ∃ i : Fin n,
    (cutBoundaryEdge g x i ∧ y = x + cubeUnit n i) ∨
      (cutBoundaryEdge g y i ∧ x = y + cubeUnit n i)

def cutBoundaryC4Free {n : ℕ} (g : CubeVertex n → Bool) : Prop :=
  ¬ ∃ v₀ v₁ v₂ v₃ : CubeVertex n,
      v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      cutBoundaryAdj g v₀ v₁ ∧ cutBoundaryAdj g v₁ v₂ ∧
      cutBoundaryAdj g v₂ v₃ ∧ cutBoundaryAdj g v₃ v₀

def coordinateSquareBase (n : ℕ) (x : CubeVertex n) (i j : Fin n) : Prop :=
  i < j ∧ x i = 0 ∧ x j = 0

def squareBoundaryCount {n : ℕ} (g : CubeVertex n → Bool)
    (x : CubeVertex n) (i j : Fin n) : ℕ :=
  (if cutBoundaryEdge g x i then 1 else 0) +
    (if cutBoundaryEdge g x j then 1 else 0) +
    (if cutBoundaryEdge g (x + cubeUnit n j) i then 1 else 0) +
    (if cutBoundaryEdge g (x + cubeUnit n i) j then 1 else 0)

def coordinateSquares (n : ℕ) :
    Finset (CubeVertex n × Fin n × Fin n) :=
  Finset.univ.filter (fun s => coordinateSquareBase n s.1 s.2.1 s.2.2)

def cutBoundarySquareParity : Prop :=
  ∀ (n : ℕ) (g : CubeVertex n → Bool)
    (s : CubeVertex n × Fin n × Fin n),
    s ∈ coordinateSquares n →
      Even (squareBoundaryCount g s.1 s.2.1 s.2.2) ∧
        (cutBoundaryC4Free g →
          squareBoundaryCount g s.1 s.2.1 s.2.2 ≠ 4 ∧
            (squareBoundaryCount g s.1 s.2.1 s.2.2 = 0 ∨
              squareBoundaryCount g s.1 s.2.1 s.2.2 = 2))

def cubeEdgeSet (n : ℕ) : Finset (CubeVertex n × Fin n) :=
  Finset.univ.filter (fun e => e.1 e.2 = 0)

def cutBoundarySquareIncidence : Prop :=
  ∀ (n : ℕ) (g : CubeVertex n → Bool),
    (cutBoundaryEdgeSet g).card * (n - 1) =
      ∑ s ∈ coordinateSquares n, squareBoundaryCount g s.1 s.2.1 s.2.2

def halfDensityBound : Prop :=
  ∀ (n : ℕ) (g : CubeVertex n → Bool),
    2 ≤ n → cutBoundaryC4Free g →
      (cutBoundaryEdgeSet g).card ≤ n * 2 ^ (n - 2) ∧
        (coordinateSquares n).card = n.choose 2 * 2 ^ (n - 2) ∧
          (cubeEdgeSet n).card = n * 2 ^ (n - 1) ∧
            (cutBoundaryEdgeSet g).card * (n - 1) =
              ∑ s ∈ coordinateSquares n, squareBoundaryCount g s.1 s.2.1 s.2.2 ∧
                2 * (n * 2 ^ (n - 2)) = (cubeEdgeSet n).card

def halfDensityEqualityCriterion : Prop :=
  ∀ (n : ℕ) (g : CubeVertex n → Bool),
    2 ≤ n → cutBoundaryC4Free g →
      ((cutBoundaryEdgeSet g).card = n * 2 ^ (n - 2) ↔
        ∀ s ∈ coordinateSquares n,
          squareBoundaryCount g s.1 s.2.1 s.2.2 = 2)

def edgeSetAdj {n : ℕ} (E : Finset (CubeVertex n × Fin n))
    (x y : CubeVertex n) : Prop :=
  ∃ i : Fin n,
    (((x, i) ∈ E ∧ y = x + cubeUnit n i) ∨
      ((y, i) ∈ E ∧ x = y + cubeUnit n i))

def edgeSetC4Free {n : ℕ} (E : Finset (CubeVertex n × Fin n)) : Prop :=
  ¬ ∃ v₀ v₁ v₂ v₃ : CubeVertex n,
      v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      edgeSetAdj E v₀ v₁ ∧ edgeSetAdj E v₁ v₂ ∧
      edgeSetAdj E v₂ v₃ ∧ edgeSetAdj E v₃ v₀

def edgeSquareCount {n : ℕ} (E : Finset (CubeVertex n × Fin n))
    (x : CubeVertex n) (i j : Fin n) : ℕ :=
  (if (x, i) ∈ E then 1 else 0) +
    (if (x, j) ∈ E then 1 else 0) +
    (if (x + cubeUnit n j, i) ∈ E then 1 else 0) +
    (if (x + cubeUnit n i, j) ∈ E then 1 else 0)

def isCutBoundary {n : ℕ} (E : Finset (CubeVertex n × Fin n)) : Prop :=
  ∃ g : CubeVertex n → Bool, E = cutBoundaryEdgeSet g

def qTwoThreeEdgeWarning : Prop :=
  let E := (cubeEdgeSet 2).erase (0, (0 : Fin 2))
  edgeSetC4Free E ∧
    E.card = 3 ∧
    4 * E.card = 3 * (cubeEdgeSet 2).card ∧
    edgeSquareCount E 0 (0 : Fin 2) (1 : Fin 2) = 3 ∧
    ¬ isCutBoundary E

def laterWeight (a : ℕ) : ℚ :=
  (a : ℚ) / (2 : ℚ) ^ a

def laterIndexRepresentation (n : ℕ) : Prop :=
  ∃ T : Finset ℕ,
    2 ≤ T.card ∧
      (∀ a ∈ T, n < a) ∧
        laterWeight n = ∑ a ∈ T, laterWeight a

def carryDigit (D : Finset ℕ) (d : ℕ) : ℕ :=
  if d ∈ D then 1 else 0

def carryR (n : ℕ) (D : Finset ℕ) : ℕ → ℤ
  | 0 => (n : ℤ)
  | d + 1 =>
      2 * carryR n D d - (n + d + 1 : ℤ) * (carryDigit D (d + 1) : ℤ)

def carryRepresentation (n : ℕ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ),
    2 ≤ D.card ∧
      (∀ d ∈ D, 0 < d) ∧
        m ∈ D ∧
          (∀ d ∈ D, d ≤ m) ∧
            carryR n D m = 0 ∧ carryDigit D m = 1 ∧
              (∀ d : ℕ, carryDigit D d = 0 ∨ carryDigit D d = 1)

def laterIndexCarryEquivalence : Prop :=
  (∀ n : ℕ, 3 ≤ n →
    (laterIndexRepresentation n ↔ carryRepresentation n)) ∧
    (∀ (n : ℕ) (D : Finset ℕ) (m : ℕ),
      3 ≤ n → 2 ≤ D.card → (∀ d ∈ D, 0 < d) → m ∈ D →
        (∀ d ∈ D, d ≤ m) →
        (laterWeight n = ∑ d ∈ D, laterWeight (n + d) ↔
          carryR n D m = 0))

def c4xC3Vertex := ZMod 4 × ZMod 3

def c4xC3Connection (d : c4xC3Vertex) : Prop :=
  d = ((1 : ZMod 4), (0 : ZMod 3)) ∨
    d = ((-1 : ZMod 4), (0 : ZMod 3)) ∨
      d = ((0 : ZMod 4), (1 : ZMod 3)) ∨
        d = ((0 : ZMod 4), (-1 : ZMod 3))

def c4xC3Adj (u v : c4xC3Vertex) : Prop :=
  c4xC3Connection (v.1 - u.1, v.2 - u.2)

def relationConnected {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ u v, Relation.ReflTransGen r u v

def c4xC3FiberRelation (i j : ZMod 4) :
    Finset (ZMod 3 × ZMod 3) :=
  Finset.univ.filter (fun p => c4xC3Adj (i, p.1) (j, p.2))

def c4xC3Matching (i j : ZMod 4) :
    Finset (ZMod 3 × ZMod 3) :=
  Finset.univ.filter (fun p => p.1 = p.2)

def adjacentC4 (i j : ZMod 4) : Prop :=
  j = i + 1 ∨ j = i - 1

def connectedC4xC3BoundaryControl : Prop :=
  relationConnected c4xC3Adj ∧
    ∀ i j : ZMod 4, adjacentC4 i j →
      c4xC3FiberRelation i j = c4xC3Matching i j ∧
        (c4xC3FiberRelation i j).card = 3 ∧
          c4xC3FiberRelation i j ≠ (Finset.univ : Finset (ZMod 3 × ZMod 3)) ∧
            c4xC3FiberRelation i j ≠ ∅

end MathlibPlus.Open.Combinatorics
