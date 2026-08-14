import Mathlib

namespace MathlibPlus.Open.Combinatorics.CubeSwitching

abbrev F2 := ZMod 2
abbrev Base (n : Nat) := Fin n → F2
abbrev Vertex (n : Nat) := Base n × F2

def baseHorizontalDirection {n : Nat} (i : Fin n) (x y : Base n) : Prop :=
  x i ≠ y i ∧ ∀ j : Fin n, j ≠ i → x j = y j

def horizontalDirection {n : Nat} (i : Fin n) (a b : Vertex n) : Prop :=
  a.2 = b.2 ∧ baseHorizontalDirection i a.1 b.1

def cubeAdj {n : Nat} (a b : Vertex n) : Prop :=
  (a.2 = b.2 ∧ ∃ i : Fin n, baseHorizontalDirection i a.1 b.1) ∨
    (a.1 = b.1 ∧ a.2 ≠ b.2)

def cubeGraph (n : Nat) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel cubeAdj

def baseCubeGraph (n : Nat) : SimpleGraph (Base n) :=
  SimpleGraph.fromRel (fun x y => ∃ i : Fin n, baseHorizontalDirection i x y)

def verticalEdge {n : Nat} (a b : Vertex n) : Prop :=
  a.1 = b.1 ∧ a.2 ≠ b.2

def fiberSwitch {n : Nat} (b : Base n → F2) : Vertex n → Vertex n :=
  fun p => (p.1, p.2 + b p.1)

def horizontalProjection {n : Nat} (G : SimpleGraph (Vertex n)) : SimpleGraph (Base n) :=
  SimpleGraph.fromRel (fun x y =>
    ∃ e : F2, ∃ i : Fin n, G.Adj (x, e) (y, e) ∧ baseHorizontalDirection i x y)

def isSelectedSubgraph {n : Nat} (G : SimpleGraph (Vertex n)) : Prop :=
  ∀ ⦃a b : Vertex n⦄, G.Adj a b → (cubeGraph n).Adj a b

def constantOnComponents {n : Nat} (P : SimpleGraph (Base n))
    (b : Base n → F2) : Prop :=
  ∀ ⦃x y : Base n⦄, P.Reachable x y → b x = b y

def mapsSelectedEdgesIntoCube {n : Nat} (G : SimpleGraph (Vertex n))
    (b : Base n → F2) : Prop :=
  ∀ ⦃a c : Vertex n⦄, G.Adj a c →
    (cubeGraph n).Adj (fiberSwitch b a) (fiberSwitch b c)

def switchedGraph {n : Nat} (G : SimpleGraph (Vertex n)) (b : Base n → F2) :
    SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel (fun x y =>
    ∃ a c, G.Adj a c ∧ fiberSwitch b a = x ∧ fiberSwitch b c = y)

def fourDistinct {α : Type} (a b c d : α) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

def c4Free {n : Nat} (G : SimpleGraph (Vertex n)) : Prop :=
  ¬ ∃ a b c d : Vertex n,
    fourDistinct a b c d ∧ G.Adj a b ∧ G.Adj b c ∧
      G.Adj c d ∧ G.Adj d a

noncomputable def directionalEdgeCount {n : Nat} (G : SimpleGraph (Vertex n))
    (i : Fin n) : Nat :=
  Nat.card {p : Vertex n × Vertex n //
    G.Adj p.1 p.2 ∧ horizontalDirection i p.1 p.2}

noncomputable def directionalDensity {n : Nat} (G : SimpleGraph (Vertex n))
    (i : Fin n) : ℚ :=
  (directionalEdgeCount G i : ℚ) /
    (2 * Fintype.card (Base n) : ℚ)

def admissibleSwitchingSpace {n : Nat} (P : SimpleGraph (Base n)) :=
  {b : Base n → F2 // constantOnComponents P b}

/-- Claim 36082: the Boolean fiber map on the decomposition into a base and the
last coordinate is the stated layer switch. -/
def codimensionOneBooleanFiberSwitching : Prop :=
  ∀ (n : Nat) (b : Base n → F2) (x : Base n) (e : F2),
    fiberSwitch b (x, e) = (x, e + b x)

/-- Claim 36083: the horizontal projection is the graph obtained from the
horizontal lifts in either z-layer. -/
def selectedHorizontalProjection : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Vertex n)) (x y : Base n),
    (horizontalProjection G).Adj x y ↔
      x ≠ y ∧
        ((∃ e : F2, ∃ i : Fin n,
            G.Adj (x, e) (y, e) ∧ baseHorizontalDirection i x y) ∨
          (∃ e : F2, ∃ i : Fin n,
            G.Adj (y, e) (x, e) ∧ baseHorizontalDirection i y x))

/-- Claim 36084: Boolean switching is admissible exactly when its bit is
constant on every component of the selected horizontal projection. -/
def exactSwitchingAdmissibilityCriterion : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Vertex n)) (b : Base n → F2),
    isSelectedSubgraph G →
      (mapsSelectedEdgesIntoCube G b ↔
        constantOnComponents (horizontalProjection G) b)

/-- Claim 36085: the component-wise switching description, edge-direction
invariants, graph isomorphism, switching-space description, and C4 invariant. -/
def structureAndInvariantsOfAdmissibleSwitchings : Prop :=
  ∀ (n : Nat) (G : SimpleGraph (Vertex n)) (b : Base n → F2),
    isSelectedSubgraph G →
      constantOnComponents (horizontalProjection G) b →
      (Function.Bijective (fiberSwitch b) ∧
        (∀ ⦃a c : Vertex n⦄, G.Adj a c → verticalEdge a c →
          ((fiberSwitch b a = a ∧ fiberSwitch b c = c) ∨
            (fiberSwitch b a = c ∧ fiberSwitch b c = a))) ∧
        (∀ ⦃i : Fin n⦄ ⦃a c : Vertex n⦄,
          G.Adj a c → horizontalDirection i a c →
            horizontalDirection i (fiberSwitch b a) (fiberSwitch b c)) ∧
        (∀ i : Fin n,
          directionalEdgeCount G i = directionalEdgeCount (switchedGraph G b) i ∧
          directionalDensity G i = directionalDensity (switchedGraph G b) i) ∧
        (∀ a c : Vertex n,
          G.Adj a c ↔
            (switchedGraph G b).Adj (fiberSwitch b a) (fiberSwitch b c)) ∧
        (∃ e : admissibleSwitchingSpace (horizontalProjection G) ≃
            ((horizontalProjection G).ConnectedComponent → F2),
          ∀ (q : admissibleSwitchingSpace (horizontalProjection G)) (x : Base n),
            e q ((horizontalProjection G).connectedComponentMk x) = q.1 x) ∧
        (c4Free G ↔ c4Free (switchedGraph G b)))

/-- Claim 36086: the full coordinate cube has connected horizontal projection,
so normalization at the zero vertex removes every nontrivial switch. -/
def fullCubeHasNoNormalizedNontrivialSwitching : Prop :=
  ∀ n : Nat,
    horizontalProjection (cubeGraph n) = baseCubeGraph n ∧
      (∀ x y : Base n, (baseCubeGraph n).Reachable x y) ∧
      (∀ b : Base n → F2,
        constantOnComponents (horizontalProjection (cubeGraph n)) b →
          b 0 = 0 → b = 0)

end MathlibPlus.Open.Combinatorics.CubeSwitching
