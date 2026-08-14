import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Combinatorics.CubeEdgeBatch

/-! The finite cube is represented exactly by Boolean vertices and by the
    canonical representatives of direction edges and coordinate squares. -/

abbrev Vertex (n : ℕ) := Fin n → Bool

abbrev CubeEdge (n : ℕ) := {e : (Vertex n × Fin n) // e.1 e.2 = false}

abbrev CubeSquare (n : ℕ) :=
  {s : (Fin n × Fin n) × Vertex n //
    s.1.1 < s.1.2 ∧ s.2 s.1.1 = false ∧ s.2 s.1.2 = false}

abbrev EdgeFunction (n : ℕ) := CubeEdge n → Bool

abbrev VertexFunction (n : ℕ) := Vertex n → Bool

namespace CubeEdge

abbrev base {n : ℕ} (e : CubeEdge n) : Vertex n := e.1.1
abbrev direction {n : ℕ} (e : CubeEdge n) : Fin n := e.1.2

end CubeEdge

namespace CubeSquare

abbrev first {n : ℕ} (s : CubeSquare n) : Fin n := s.1.1.1
abbrev second {n : ℕ} (s : CubeSquare n) : Fin n := s.1.1.2
abbrev base {n : ℕ} (s : CubeSquare n) : Vertex n := s.1.2

end CubeSquare

def flipCoord {n : ℕ} (x : Vertex n) (i : Fin n) : Vertex n :=
  Function.update x i (Bool.not (x i))

def addVertex {n : ℕ} (x a : Vertex n) : Vertex n :=
  fun i => Bool.xor (x i) (a i)

def representedEdge {n : ℕ} (x : Vertex n) (i : Fin n) : CubeEdge n :=
  ⟨(Function.update x i false, i), by simp⟩

def edgeIndicator {n : ℕ} (F : EdgeFunction n) (i : Fin n) (x : Vertex n) : Bool :=
  F (representedEdge x i)

def xor2 (a b : Bool) : Bool := Bool.xor a b

def xor3 (a b c : Bool) : Bool := xor2 (xor2 a b) c

def xor4 (a b c d : Bool) : Bool := xor2 (xor2 a b) (xor2 c d)

def curlAt {n : ℕ} (F : EdgeFunction n) (i j : Fin n) (x : Vertex n) : Bool :=
  xor4 (edgeIndicator F i x)
    (edgeIndicator F i (flipCoord x j))
    (edgeIndicator F j x)
    (edgeIndicator F j (flipCoord x i))

def oddSquareCount {n : ℕ} (F : EdgeFunction n) : ℕ :=
  (Finset.univ.filter (fun s : CubeSquare n =>
    curlAt F s.first s.second s.base = true)).card

def squareEdges {n : ℕ} (s : CubeSquare n) : Finset (CubeEdge n) :=
  {representedEdge s.base s.first,
   representedEdge s.base s.second,
   representedEdge (flipCoord s.base s.first) s.second,
   representedEdge (flipCoord s.base s.second) s.first}

def squareEdgeCount {n : ℕ} (F : EdgeFunction n) (s : CubeSquare n) : ℕ :=
  ((squareEdges s).filter (fun e => F e = true)).card

def edgeCount {n : ℕ} (F : EdgeFunction n) : ℕ :=
  (Finset.univ.filter (fun e : CubeEdge n => F e = true)).card

def activeIndices {n : ℕ} (x : Vertex n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = true)

def below {n : ℕ} (x : Vertex n) (j : Fin n) : Vertex n :=
  fun k => if k < j then x k else false

def boolParityFinset {α : Type} (s : Finset α) (p : α → Bool) : Bool :=
  decide ((∑ a ∈ s, if p a then (1 : ZMod 2) else 0) = 1)

def canonicalVertexFunction {n : ℕ} (F : EdgeFunction n) : VertexFunction n :=
  fun x => boolParityFinset (activeIndices x)
    (fun j => edgeIndicator F j (below x j))

def residualAt {n : ℕ} (F : EdgeFunction n) (g : VertexFunction n)
    (i : Fin n) (x : Vertex n) : Bool :=
  xor3 (edgeIndicator F i x) (g x) (g (flipCoord x i))

def cutBoundary {n : ℕ} (g : VertexFunction n) : EdgeFunction n :=
  fun e => xor2 (g e.base) (g (flipCoord e.base e.direction))

def residualEdge {n : ℕ} (F : EdgeFunction n) (g : VertexFunction n) : EdgeFunction n :=
  fun e => residualAt F g e.direction e.base

def symmetricDifference {n : ℕ} (F H : EdgeFunction n) : EdgeFunction n :=
  fun e => xor2 (F e) (H e)

def residualWeight {n : ℕ} (F : EdgeFunction n) (g : VertexFunction n) : ℕ :=
  edgeCount (symmetricDifference F (cutBoundary g))

def translatedEdge {n : ℕ} (a : Vertex n) (e : CubeEdge n) : CubeEdge n :=
  representedEdge (addVertex e.base a) e.direction

def translatedFunction {n : ℕ} (F : EdgeFunction n) (a : Vertex n) : EdgeFunction n :=
  fun e => F (translatedEdge a e)

def canonicalResidualWeight {n : ℕ} (F : EdgeFunction n) (a : Vertex n) : ℕ :=
  residualWeight (translatedFunction F a) (canonicalVertexFunction (translatedFunction F a))

def expectedCanonicalResidualWeight {n : ℕ} (F : EdgeFunction n) : ℚ :=
  (∑ a : Vertex n, (canonicalResidualWeight F a : ℚ)) /
    (Fintype.card (Vertex n) : ℚ)

def curlConstantOnSquare {n : ℕ} (F : EdgeFunction n) (s : CubeSquare n) : Prop :=
  let i := s.first
  let j := s.second
  let x := s.base
  curlAt F i j x = curlAt F i j (flipCoord x i) ∧
  curlAt F i j x = curlAt F i j (flipCoord x j) ∧
  curlAt F i j x = curlAt F i j (flipCoord (flipCoord x i) j)

def claim_51874 : Prop :=
  ∀ (n : ℕ) (F : EdgeFunction n) (s : CubeSquare n),
    curlConstantOnSquare F s

def pathIdentityAt {n : ℕ} (F : EdgeFunction n) (i : Fin n) (x : Vertex n) : Prop :=
  x i = false →
    residualAt F (canonicalVertexFunction F) i x =
      boolParityFinset
        (Finset.univ.filter (fun j : Fin n => i < j ∧ x j = true))
        (fun j => curlAt F i j (below x j))

def residualSupportIdentity {n : ℕ} (F : EdgeFunction n) : Prop :=
  ∀ e : CubeEdge n,
    residualEdge F (canonicalVertexFunction F) e =
      symmetricDifference F (cutBoundary (canonicalVertexFunction F)) e

def claim_51876 : Prop :=
  ∀ (n : ℕ) (F : EdgeFunction n),
    (∀ (i : Fin n) (x : Vertex n), pathIdentityAt F i x) ∧
    residualSupportIdentity F

def oddSquareCountForPair {n : ℕ} (F : EdgeFunction n) (i j : Fin n) : ℕ :=
  (Finset.univ.filter (fun s : CubeSquare n =>
    s.first = i ∧ s.second = j ∧ curlAt F i j s.base = true)).card

def displayedPairContribution {n : ℕ} (F : EdgeFunction n) (a : Vertex n)
    (i j : Fin n) : ℕ :=
  (Finset.univ.filter (fun e : CubeEdge n =>
    e.direction = i ∧ i < j ∧ e.base j = true ∧
      curlAt (translatedFunction F a) i j (below e.base j) = true)).card

def expectedDisplayedPairContribution {n : ℕ} (F : EdgeFunction n)
    (i j : Fin n) : ℚ :=
  (∑ a : Vertex n, (displayedPairContribution F a i j : ℚ)) /
    (Fintype.card (Vertex n) : ℚ)

def claim_51878 : Prop :=
  ∀ (n : ℕ) (F : EdgeFunction n),
    (∀ (i j : Fin n), i < j →
      expectedDisplayedPairContribution F i j =
        (oddSquareCountForPair F i j : ℚ)) ∧
    expectedCanonicalResidualWeight F ≤ (oddSquareCount F : ℚ) ∧
    ∃ g : VertexFunction n, residualWeight F g ≤ oddSquareCount F

def claim_51880 : Prop :=
  ∀ (n : ℕ) (F : EdgeFunction n),
    (∀ s : CubeSquare n, curlAt F s.first s.second s.base = false) →
      ∃ g : VertexFunction n,
        F = cutBoundary g

def fullSquareCount {n : ℕ} (F : EdgeFunction n) : ℕ :=
  (Finset.univ.filter (fun s : CubeSquare n => squareEdgeCount F s = 4)).card

def coordinateSquareCount (n : ℕ) : ℕ :=
  Nat.choose n 2 * 2 ^ (n - 2)

def totalCubeEdgeCount (n : ℕ) : ℕ :=
  n * 2 ^ (n - 1)

def c4Free {n : ℕ} (F : EdgeFunction n) : Prop :=
  ∀ s : CubeSquare n, squareEdgeCount F s ≠ 4

def cutHasEvenSquareIntersection {n : ℕ} (g : VertexFunction n) : Prop :=
  ∀ s : CubeSquare n,
    squareEdgeCount (cutBoundary g) s = 0 ∨
    squareEdgeCount (cutBoundary g) s = 2 ∨
    squareEdgeCount (cutBoundary g) s = 4

def claim_51881 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (F : EdgeFunction n), c4Free F →
    Fintype.card (CubeSquare n) = coordinateSquareCount n ∧
    ∃ g : VertexFunction n,
      let H := cutBoundary g
      let X := symmetricDifference F H
      edgeCount X ≤ oddSquareCount F ∧
      cutHasEvenSquareIntersection g ∧
      (∀ s : CubeSquare n,
        squareEdgeCount H s = 4 → squareEdgeCount X s > 0) ∧
      (∀ e : CubeEdge n,
        (Finset.univ.filter (fun s : CubeSquare n => e ∈ squareEdges s)).card = n - 1) ∧
      (n - 1) * edgeCount H =
        (∑ s : CubeSquare n, squareEdgeCount H s) ∧
      fullSquareCount H ≤ (n - 1) * edgeCount X ∧
      (n - 1) * edgeCount H ≤
        2 * coordinateSquareCount n + 2 * fullSquareCount H ∧
      edgeCount H ≤ totalCubeEdgeCount n / 2 + 2 * edgeCount X

def edgeDensity {n : ℕ} (F : EdgeFunction n) : ℝ :=
  (edgeCount F : ℝ) / (totalCubeEdgeCount n : ℝ)

def oddCurlDensity {n : ℕ} (F : EdgeFunction n) : ℝ :=
  (oddSquareCount F : ℝ) / (coordinateSquareCount n : ℝ)

def claim_51882 : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (F : EdgeFunction n), c4Free F →
    edgeCount F ≤ n * 2 ^ (n - 2) + 3 * oddSquareCount F

def claim_51884 : Prop :=
  (∀ (n : ℕ), 2 ≤ n → ∀ (F : EdgeFunction n), c4Free F →
    edgeDensity F ≤ (1 / 2 : ℝ) +
      3 * (n - 1 : ℕ) * oddCurlDensity F / 4) ∧
  (∀ (F : ∀ n : ℕ, EdgeFunction n),
    (∀ n : ℕ, 2 ≤ n → c4Free (F n)) →
    Asymptotics.IsLittleO Filter.atTop
      (fun n => oddCurlDensity (F n))
      (fun n => (1 : ℝ) / (n : ℝ)) →
    Filter.limsup (fun n => edgeDensity (F n)) Filter.atTop ≤ (1 / 2 : ℝ))

end MathlibPlus.Open.Combinatorics.CubeEdgeBatch

end
