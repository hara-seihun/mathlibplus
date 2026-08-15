import Mathlib

namespace MathlibPlus.Open

abbrev HypercubeVertex (n : ℕ) := Fin n → Bool
abbrev HypercubeEdge (n : ℕ) := Sym2 (HypercubeVertex n)

def hypercubeFlipAt {n : ℕ} (v : HypercubeVertex n) (i : Fin n) : HypercubeVertex n :=
  Function.update v i (!v i)

def hypercubeAdjacent {n : ℕ} (v w : HypercubeVertex n) : Prop :=
  ∃ i : Fin n, v i ≠ w i ∧ ∀ j : Fin n, j ≠ i → v j = w j

def hypercubeGraph (n : ℕ) : SimpleGraph (HypercubeVertex n) :=
  SimpleGraph.fromRel hypercubeAdjacent

def coordinateSquare {n : ℕ} (v : HypercubeVertex n) (i j : Fin n) : Finset (HypercubeEdge n) :=
  {Sym2.mk v (hypercubeFlipAt v i),
    Sym2.mk v (hypercubeFlipAt v j),
    Sym2.mk (hypercubeFlipAt v i) (hypercubeFlipAt (hypercubeFlipAt v i) j),
    Sym2.mk (hypercubeFlipAt v j) (hypercubeFlipAt (hypercubeFlipAt v j) i)}

def coordinateSquareFamily (n : ℕ) : Set (Finset (HypercubeEdge n)) :=
  {S | ∃ (v : HypercubeVertex n) (i j : Fin n), i < j ∧ v i = false ∧ v j = false ∧
    S = coordinateSquare v i j}

def oddCoordinateSquareCover {n : ℕ} (H : Finset (HypercubeEdge n)) : Prop :=
  (∀ e ∈ H, e ∈ (hypercubeGraph n).edgeSet) ∧
    (∀ (v : HypercubeVertex n) (i j : Fin n), i < j → v i = false → v j = false →
      (H ∩ coordinateSquare v i j).card % 2 = 1)

noncomputable def minimumOddCoordinateSquareCoverSize (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ H : Finset (HypercubeEdge n), oddCoordinateSquareCover H ∧ H.card = k}

noncomputable def oddSquareInsertionCost {n : ℕ} (M : Finset (HypercubeEdge n)) : ℕ :=
  sInf {r : ℕ | ∃ H : Finset (HypercubeEdge n), oddCoordinateSquareCover H ∧
    (H \ M).card = r}

def minimumOddCoordinateSquareCoverAndInsertionCost : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (∃ H : Finset (HypercubeEdge n), oddCoordinateSquareCover H ∧
      H.card = minimumOddCoordinateSquareCoverSize n) ∧
    (∀ M : Finset (HypercubeEdge n),
      ∃ H : Finset (HypercubeEdge n), oddCoordinateSquareCover H ∧
        (H \ M).card = oddSquareInsertionCost M)

def universalOddSquareInsertionLowerBound : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ M : Finset (HypercubeEdge n),
    (∀ e ∈ M, e ∈ (hypercubeGraph n).edgeSet) →
      oddSquareInsertionCost M ≥
        minimumOddCoordinateSquareCoverSize n - M.card

end MathlibPlus.Open
