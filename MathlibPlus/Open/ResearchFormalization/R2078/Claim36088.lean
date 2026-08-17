import MathlibPlus.Open.Combinatorics.CubeSwitching

namespace MathlibPlus.Open.ResearchFormalization.R2078DensityCounterfeit

open MathlibPlus.Open.Combinatorics.CubeSwitching

/-- The graph having exactly the unordered edge represented by `p,q`. -/
def oneEdgeGraph {n : ℕ} (p q : Vertex n) : SimpleGraph (Vertex n) :=
  SimpleGraph.fromRel (fun a c => a = p ∧ c = q)

def e₁ : Base 2 := Pi.single 0 1

def e₂ : Base 2 := Pi.single 1 1

def nearGraph : SimpleGraph (Vertex 2) :=
  oneEdgeGraph (0, 0) (e₁, 0)

def farGraph : SimpleGraph (Vertex 2) :=
  oneEdgeGraph (e₂, 0) (e₁ + e₂, 0)

/-- The indicator of the base vertex `00`. -/
def baseVertexIndicator : Base 2 → F2 :=
  fun x => if x = 0 then 1 else 0

/-- The vertical direction count in the three-dimensional cube carrier. -/
noncomputable def verticalDirectionalEdgeCount
    (G : SimpleGraph (Vertex 2)) : ℕ :=
  Nat.card {p : Vertex 2 × Vertex 2 //
    G.Adj p.1 p.2 ∧ verticalEdge p.1 p.2}

noncomputable def verticalDirectionalDensity
    (G : SimpleGraph (Vertex 2)) : ℚ :=
  (verticalDirectionalEdgeCount G : ℚ) /
    (2 * Fintype.card (Base 2) : ℚ)

/-- The three-coordinate density vector, with the last coordinate the fixed
fiber direction `z`. -/
noncomputable def densityVector3
    (G : SimpleGraph (Vertex 2)) : Fin 3 → ℚ :=
  Fin.cases (directionalDensity G 0)
    (fun i => Fin.cases (directionalDensity G 1)
      (fun _ => verticalDirectionalDensity G) i)

/-- Thresholded coordinate directions, the connection-set data retained by a
threshold Cayley comparison. -/
noncomputable def thresholdDirections
    (G : SimpleGraph (Vertex 2)) (τ : ℚ) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => τ ≤ densityVector3 G i)

/-- The standard coordinate generator corresponding to one direction. -/
def unitDirection (i : Fin 3) : Fin 3 → F2 :=
  fun j => if i = j then 1 else 0

/-- Thresholded coordinate generators, rather than only their direction
indices. -/
noncomputable def thresholdConnectionSet
    (G : SimpleGraph (Vertex 2)) (τ : ℚ) : Finset (Fin 3 → F2) :=
  (thresholdDirections G τ).image unitDirection

/-- Claim 36088: equal density and threshold data can coexist with opposite
literal fixed-cube switching behavior. -/
def densityProjectionCounterfeit_claim36088 : Prop :=
  isSelectedSubgraph nearGraph ∧
    isSelectedSubgraph farGraph ∧
    c4Free nearGraph ∧
    c4Free farGraph ∧
    (∀ i : Fin 3, densityVector3 nearGraph i = densityVector3 farGraph i) ∧
    densityVector3 nearGraph 0 = 1 / 4 ∧
    densityVector3 nearGraph 1 = 0 ∧
    densityVector3 nearGraph 2 = 0 ∧
    densityVector3 farGraph 0 = 1 / 4 ∧
    densityVector3 farGraph 1 = 0 ∧
    densityVector3 farGraph 2 = 0 ∧
    (∀ τ : ℚ, thresholdDirections nearGraph τ = thresholdDirections farGraph τ) ∧
    (∀ τ : ℚ,
      thresholdConnectionSet nearGraph τ = thresholdConnectionSet farGraph τ) ∧
    (horizontalProjection nearGraph).Adj (0 : Base 2) e₁ ∧
    (horizontalProjection farGraph).Adj e₂ (e₁ + e₂) ∧
    baseVertexIndicator 0 = 1 ∧
    baseVertexIndicator e₁ = 0 ∧
    fiberSwitch baseVertexIndicator (0, 0) = (0, 1) ∧
    fiberSwitch baseVertexIndicator (e₁, 0) = (e₁, 0) ∧
    fiberSwitch baseVertexIndicator (e₁, 0) -
        fiberSwitch baseVertexIndicator (0, 0) = (e₁, 1) ∧
    ¬(cubeGraph 2).Adj
      (fiberSwitch baseVertexIndicator (0, 0))
      (fiberSwitch baseVertexIndicator (e₁, 0)) ∧
    ¬mapsSelectedEdgesIntoCube nearGraph baseVertexIndicator ∧
    baseVertexIndicator e₂ = baseVertexIndicator (e₁ + e₂) ∧
    fiberSwitch baseVertexIndicator (e₂, 0) = (e₂, 0) ∧
    fiberSwitch baseVertexIndicator (e₁ + e₂, 0) = (e₁ + e₂, 0) ∧
    fiberSwitch baseVertexIndicator (e₁ + e₂, 0) -
        fiberSwitch baseVertexIndicator (e₂, 0) = (e₁, 0) ∧
    (cubeGraph 2).Adj
      (fiberSwitch baseVertexIndicator (e₂, 0))
      (fiberSwitch baseVertexIndicator (e₁ + e₂, 0)) ∧
    mapsSelectedEdgesIntoCube farGraph baseVertexIndicator

end MathlibPlus.Open.ResearchFormalization.R2078DensityCounterfeit
