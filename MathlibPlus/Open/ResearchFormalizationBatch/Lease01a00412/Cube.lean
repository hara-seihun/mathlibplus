import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.Cube

open scoped BigOperators

noncomputable section

open Classical

abbrev CubeVertex (n : ℕ) := Fin n → Bool

def lowerVertex {n : ℕ} (i : Fin n) (x : CubeVertex n) : CubeVertex n :=
  Function.update x i false

def toggleVertex {n : ℕ} (i : Fin n) (x : CubeVertex n) : CubeVertex n :=
  Function.update x i (Bool.not (x i))

def CubeEdge (n : ℕ) :=
  {e : Fin n × CubeVertex n // e.2 e.1 = false}

def cubeEdge {n : ℕ} (i : Fin n) (x : CubeVertex n) : CubeEdge n :=
  ⟨(i, lowerVertex i x), by simp [lowerVertex]⟩

def edgeDirection {n : ℕ} (e : CubeEdge n) : Fin n := e.1.1

def edgeLower {n : ℕ} (e : CubeEdge n) : CubeVertex n := e.1.2

def edgeUpper {n : ℕ} (e : CubeEdge n) : CubeVertex n :=
  toggleVertex (edgeDirection e) (edgeLower e)

def CubeSlice (n : ℕ) (i : Fin n) :=
  {x : CubeVertex n // x i = false}

instance cubeEdgeFintype (n : ℕ) : Fintype (CubeEdge n) :=
  Fintype.subtype
    ((Finset.univ : Finset (Fin n × CubeVertex n)).filter
      (fun e => e.2 e.1 = false)) (by simp)
instance cubeSliceFintype (n : ℕ) (i : Fin n) : Fintype (CubeSlice n i) :=
  Fintype.subtype
    ((Finset.univ : Finset (CubeVertex n)).filter (fun x => x i = false)) (by simp)

instance cubeEdgeDecidableEq (n : ℕ) : DecidableEq (CubeEdge n) := Classical.decEq _

def sliceExpectation {n : ℕ} (G : Finset (CubeEdge n)) (i : Fin n) : ℚ :=
  (∑ x : CubeSlice n i, if cubeEdge i x.1 ∈ G then 1 else 0) /
    (Fintype.card (CubeSlice n i) : ℚ)

def selectedSquare {n : ℕ} (G : Finset (CubeEdge n)) : Prop :=
  ∃ (i j : Fin n) (x : CubeVertex n),
    i < j ∧ x i = false ∧ x j = false ∧
      cubeEdge i x ∈ G ∧
      cubeEdge i (toggleVertex j x) ∈ G ∧
      cubeEdge j x ∈ G ∧
      cubeEdge j (toggleVertex i x) ∈ G

def cubeC4Free {n : ℕ} (G : Finset (CubeEdge n)) : Prop :=
  ¬ selectedSquare G

/-- Coordinate edge-function model and the exact square criterion (Claim 16220). -/
def claim16220 : Prop :=
  ∀ (n : ℕ) (G : Finset (CubeEdge n)),
    (G.card : ℚ) =
      (2 : ℚ) ^ (n - 1) * ∑ i : Fin n, sliceExpectation G i ∧
    (cubeC4Free G ↔
      ∀ (i j : Fin n) (x : CubeVertex n),
        i < j → x i = false → x j = false →
          (if cubeEdge i x ∈ G then (1 : ℚ) else 0) *
            (if cubeEdge i (toggleVertex j x) ∈ G then (1 : ℚ) else 0) *
            (if cubeEdge j x ∈ G then (1 : ℚ) else 0) *
            (if cubeEdge j (toggleVertex i x) ∈ G then (1 : ℚ) else 0) = 0)

/-- Coordinate squares are the four canonical edges based at a lower corner. -/
def CubeSquare (n : ℕ) :=
  {s : Fin n × Fin n × CubeVertex n //
    s.1 < s.2.1 ∧ s.2.2 s.1 = false ∧ s.2.2 s.2.1 = false}

instance cubeSquareFintype (n : ℕ) : Fintype (CubeSquare n) :=
  Fintype.subtype
    ((Finset.univ : Finset (Fin n × Fin n × CubeVertex n)).filter
      (fun s => s.1 < s.2.1 ∧ s.2.2 s.1 = false ∧ s.2.2 s.2.1 = false)) (by simp)

def squareEdges {n : ℕ} (s : CubeSquare n) : Finset (CubeEdge n) :=
  insert (cubeEdge s.1.1 s.1.2.2)
    (insert (cubeEdge s.1.1 (toggleVertex s.1.2.1 s.1.2.2))
      (insert (cubeEdge s.1.2.1 s.1.2.2)
        {cubeEdge s.1.2.1 (toggleVertex s.1.1 s.1.2.2)}))

def oddSquareCount {n : ℕ} (F : Finset (CubeEdge n)) : ℕ :=
  (Finset.univ.filter (fun s : CubeSquare n =>
    (F.filter (fun e => e ∈ squareEdges s)).card % 2 = 1)).card

def cutSet {n : ℕ} (g : CubeVertex n → Bool) : Finset (CubeEdge n) :=
  Finset.univ.filter (fun e : CubeEdge n => g (edgeLower e) ≠ g (edgeUpper e))

def symmetricDifferenceCard {n : ℕ}
    (F H : Finset (CubeEdge n)) : ℕ :=
  (F.filter (fun e => e ∉ H)).card + (H.filter (fun e => e ∉ F)).card

def cutDistance {n : ℕ} (F : Finset (CubeEdge n)) : ℕ :=
  (Finset.univ.image (fun g : CubeVertex n → Bool => symmetricDifferenceCard F (cutSet g))).min'
    (by simp)

/-- Odd-square gauge controls distance to a cut (Claim 16223). -/
def claim16223 : Prop :=
  ∀ (n : ℕ) (F : Finset (CubeEdge n)),
    cutDistance F ≤ oddSquareCount F

def cubeWeight {n : ℕ} (x : CubeVertex n) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i = true)).card

def alternatingEdges (n : ℕ) : Finset (CubeEdge n) :=
  Finset.univ.filter (fun e : CubeEdge n => Even (cubeWeight (edgeLower e)))

def endpoints {n : ℕ} (e : CubeEdge n) : Finset (CubeVertex n) :=
  {edgeLower e, edgeUpper e}

def isMatching {n : ℕ} (R : Finset (CubeEdge n)) : Prop :=
  ∀ e ∈ R, ∀ e' ∈ R, e ≠ e' → Disjoint (endpoints e) (endpoints e')

def complementaryEdges {n : ℕ} (R : Finset (CubeEdge n)) : Prop :=
  ∀ e ∈ R, e ∉ alternatingEdges n

def cubeEdgeCount (n : ℕ) : ℕ := n * 2 ^ (n - 1)

def maximumComplementaryMatchingSize (n : ℕ) : ℕ :=
  ∑ k ∈ (Finset.range n).filter Odd, min (Nat.choose n k) (Nat.choose n (k + 1))

/-- Alternating-layer extensions are matching-bounded (Claim 16227). -/
def claim16227 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    (∀ R : Finset (CubeEdge n), complementaryEdges R →
      (cubeC4Free (alternatingEdges n ∪ R) ↔ isMatching R)) ∧
    (∀ R : Finset (CubeEdge n), complementaryEdges R →
      cubeC4Free (alternatingEdges n ∪ R) →
        ((alternatingEdges n ∪ R).card : ℚ) ≤
          (1 / 2 + 1 / (n : ℚ)) * (cubeEdgeCount n : ℚ)) ∧
    (∀ R : Finset (CubeEdge n), complementaryEdges R →
      cubeC4Free (alternatingEdges n ∪ R) →
        R.card ≤ maximumComplementaryMatchingSize n) ∧
    ∃ R : Finset (CubeEdge n),
      complementaryEdges R ∧
        cubeC4Free (alternatingEdges n ∪ R) ∧
        R.card = maximumComplementaryMatchingSize n

end
end MathlibPlus.Open.Research.FormalizationBatch.Cube
