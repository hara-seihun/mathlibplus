import Mathlib

open scoped Classical BigOperators

namespace MathlibPlus.Open.Combinatorics

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev CubeVertex (n : ℕ) := Fin n → Bool

def bitWeight (b : Bool) : ℕ := if b then 1 else 0

def cubeLevel {n : ℕ} (x : CubeVertex n) : ℕ :=
  ∑ i : Fin n, bitWeight (x i)

def cubeAdjacent {n : ℕ} (x y : CubeVertex n) : Prop :=
  ∃ i : Fin n, x i ≠ y i ∧ ∀ j : Fin n, j ≠ i → x j = y j

def IsCubeEdge (n : ℕ) (e : Finset (CubeVertex n)) : Prop :=
  e.card = 2 ∧ ∃ x ∈ e, ∃ y ∈ e, x ≠ y ∧ cubeAdjacent x y

def CubeEdge (n : ℕ) := {e : Finset (CubeVertex n) // IsCubeEdge n e}

noncomputable instance cubeEdgeFintype (n : ℕ) : Fintype (CubeEdge n) :=
  Fintype.subtype
    (Finset.univ.filter (fun e : Finset (CubeVertex n) => IsCubeEdge n e))
    (by intro e; simp)

def edgeHasLevelPair {n : ℕ} (e : CubeEdge n) (k : ℕ) : Prop :=
  ∃ x ∈ e.1, ∃ y ∈ e.1,
    cubeAdjacent x y ∧ cubeLevel x = k ∧ cubeLevel y = k + 1

def cubeLayerVertices (n k : ℕ) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun x => cubeLevel x = k)

def cubeLayerSize (n k : ℕ) : ℕ :=
  (cubeLayerVertices n k).card

def selectedLayer (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ) : Finset (CubeEdge n) :=
  G.filter (fun e => edgeHasLevelPair e k)

def selectedLayerSize (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ) : ℕ :=
  (selectedLayer n G k).card

def allLayerEdges (n k : ℕ) : ℕ :=
  (n - k) * cubeLayerSize n k

def layerDensity (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ) : ℚ :=
  (selectedLayerSize n G k : ℚ) / (allLayerEdges n k : ℚ)

def edgeIn {n : ℕ} (G : Finset (CubeEdge n)) (x y : CubeVertex n) : Prop :=
  ∃ e ∈ G, x ∈ e.1 ∧ y ∈ e.1

def toggle {n : ℕ} (x : CubeVertex n) (i : Fin n) : CubeVertex n :=
  Function.update x i (!x i)

def squareFree {n : ℕ} (G : Finset (CubeEdge n)) : Prop :=
  ∀ (x : CubeVertex n) (i j : Fin n),
    i ≠ j → x i = false → x j = false →
      ¬ (edgeIn G x (toggle x i) ∧
        edgeIn G x (toggle x j) ∧
        edgeIn G (toggle x i) (toggle (toggle x i) j) ∧
        edgeIn G (toggle x j) (toggle (toggle x j) i))

def lowerOppositeCount (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ)
    (x : CubeVertex n) : ℕ :=
  (G.filter (fun e =>
    x ∈ e.1 ∧ ∃ y ∈ e.1,
      cubeAdjacent x y ∧ cubeLevel x = k ∧ cubeLevel y = k + 1)).card

def upperOppositeCount (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ)
    (y : CubeVertex n) : ℕ :=
  (G.filter (fun e =>
    y ∈ e.1 ∧ ∃ x ∈ e.1,
      cubeAdjacent x y ∧ cubeLevel x = k + 1 ∧ cubeLevel y = k + 2)).card

def lowerOppositeSum (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ) : ℕ :=
  Finset.sum (cubeLayerVertices n k)
    (fun x => Nat.choose (lowerOppositeCount n G k x) 2)

def upperOppositeSum (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ) : ℕ :=
  Finset.sum (cubeLayerVertices n (k + 2))
    (fun y => Nat.choose (upperOppositeCount n G k y) 2)

def quadraticLayerExpression (n k : ℕ) (a b : ℚ) : ℚ :=
  a ^ 2 * ((n - k : ℕ) : ℚ) / ((n - k - 1 : ℕ) : ℚ) +
    b ^ 2 * ((k + 2 : ℕ) : ℚ) / ((k + 1 : ℕ) : ℚ) -
    a / ((n - k - 1 : ℕ) : ℚ) - b / ((k + 1 : ℕ) : ℚ)

/-- The layer sizes, total inter-layer edge counts, and rational densities are
those of the Boolean cube; the selected graph only enters through `m_k`. -/
def claim46972 : Prop :=
  ∀ (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ),
    k ≤ n - 1 →
      cubeLayerSize n k = Nat.choose n k ∧
      allLayerEdges n k = (n - k) * cubeLayerSize n k ∧
      allLayerEdges n k = (k + 1) * cubeLayerSize n (k + 1) ∧
      layerDensity n G k =
        (selectedLayerSize n G k : ℚ) / (allLayerEdges n k : ℚ)

/-- The pointwise square count bound for a selected square-free cube edge set. -/
def claim46973 : Prop :=
  ∀ (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ),
    k ≤ n - 2 → squareFree G →
      lowerOppositeSum n G k + upperOppositeSum n G k ≤
        cubeLayerSize n k * Nat.choose (n - k) 2

/-- The convexity consequence of the pointwise square count bound, retaining
both adjacent selected-layer edge counts and the literal square premise. -/
def claim46974 : Prop :=
  ∀ (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ),
    k ≤ n - 2 → squareFree G →
      (selectedLayerSize n G k : ℚ) ^ 2 /
          (2 * (cubeLayerSize n k : ℚ)) -
        (selectedLayerSize n G k : ℚ) / 2 +
      (selectedLayerSize n G (k + 1) : ℚ) ^ 2 /
          (2 * (cubeLayerSize n (k + 2) : ℚ)) -
        (selectedLayerSize n G (k + 1) : ℚ) / 2 ≤
        (cubeLayerSize n k : ℚ) * Nat.choose (n - k) 2

/-- The target-native rational density inequality in every valid pair of
adjacent layers. -/
def claim46975 : Prop :=
  ∀ (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ),
    k ≤ n - 2 → squareFree G →
      quadraticLayerExpression n k
          (layerDensity n G k) (layerDensity n G (k + 1)) ≤ 1

/-- The quantified central-band form of the asymptotic estimate. -/
def claim46976 : Prop :=
  ∀ (eta : ℝ), 0 < eta → eta < 1 / 2 →
    ∃ C_eta : ℝ, 0 ≤ C_eta ∧ ∃ N_eta : ℕ,
      ∀ (n : ℕ), N_eta ≤ n →
        ∀ (G : Finset (CubeEdge n)), squareFree G →
          ∀ (k : ℕ),
            eta * (n : ℝ) ≤ (k : ℝ) →
            (k : ℝ) ≤ (1 - eta) * (n : ℝ) →
            (layerDensity n G k : ℝ) ^ 2 +
                (layerDensity n G (k + 1) : ℝ) ^ 2 ≤
              1 + C_eta / (n : ℝ)

/-- The scalar witness in the degree relaxation, not a claim about a selected
cube edge set. -/
def claim46977 : Prop :=
  ∀ (n k : ℕ), 4 ≤ n → k ≤ n - 2 →
    quadraticLayerExpression n k (7 / 10) (7 / 10) ≤ 1

def fixtureVertex0110 : CubeVertex 4 := ![false, true, true, false]
def fixtureVertex1000 : CubeVertex 4 := ![false, false, false, true]
def fixtureVertex0000 : CubeVertex 4 := ![false, false, false, false]
def fixtureVertex1101 : CubeVertex 4 := ![true, false, true, true]
def fixtureVertex0001 : CubeVertex 4 := ![true, false, false, false]
def fixtureVertex1010 : CubeVertex 4 := ![false, true, false, true]
def fixtureVertex0011 : CubeVertex 4 := ![true, true, false, false]
def fixtureVertex0100 : CubeVertex 4 := ![false, false, true, false]

def fixtureLowerEndpoints : Fin 4 → Finset (CubeVertex 4)
  | 0 => {fixtureVertex0110, fixtureVertex1000}
  | 1 => {fixtureVertex0000, fixtureVertex1101}
  | 2 => {fixtureVertex0001, fixtureVertex1010}
  | 3 => {fixtureVertex0011, fixtureVertex0100}

def fixtureOmitted : Finset (CubeEdge 4) :=
  Finset.univ.filter (fun e =>
    ∃ d : Fin 4, ∃ z : CubeVertex 4,
      z ∈ fixtureLowerEndpoints d ∧ e.1 = {z, toggle z d})

def fixtureSelected : Finset (CubeEdge 4) := Finset.univ \ fixtureOmitted

def fixtureLayerCounts : Fin 4 → ℕ :=
  fun k => selectedLayerSize 4 fixtureSelected k.1

def fixtureHostLayerCounts : Fin 4 → ℕ :=
  fun k => allLayerEdges 4 k.1

def fixtureDensities : Fin 4 → ℚ :=
  fun k => layerDensity 4 fixtureSelected k.1

def fixtureDensitiesAt (k : Fin 3) : ℚ :=
  fixtureDensities ⟨k.1, by omega⟩

def fixtureDensitiesNext (k : Fin 3) : ℚ :=
  fixtureDensities ⟨k.1 + 1, by omega⟩

/-- The four-dimensional omitted-edge fixture and its exact layer profile. -/
def claim46979 : Prop :=
  squareFree fixtureSelected ∧
    fixtureLayerCounts = ![3, 9, 9, 3] ∧
    fixtureHostLayerCounts = ![4, 12, 12, 4] ∧
    fixtureDensities = ![3 / 4, 3 / 4, 3 / 4, 3 / 4]

/-- The fixture refutes the linear adjacent-density strengthening while
retaining the quadratic inequality. -/
def claim46980 : Prop :=
  ¬ (∀ (n : ℕ) (G : Finset (CubeEdge n)) (k : ℕ),
      k ≤ n - 2 → squareFree G →
        layerDensity n G k + layerDensity n G (k + 1) ≤ 1) ∧
    squareFree fixtureSelected ∧
    (∀ k : Fin 3,
      fixtureDensitiesAt k + fixtureDensitiesNext k = 3 / 2) ∧
    (∀ k : Fin 3,
      quadraticLayerExpression 4 k.1
          (fixtureDensitiesAt k) (fixtureDensitiesNext k) ≤ 1)

end

end MathlibPlus.Open.Combinatorics
