import MathlibPlus.Open.ResearchFormalization.BatchR1853Claims33702_33729_33732

namespace MathlibPlus.Open.ResearchFormalization.R1853

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalization.BatchR1853
open MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev StressVertex (n : ℕ) := Fin n
abbrev StressEdge (n : ℕ) := Fin n × Fin n
abbrev StressPlane := Fin 2 → ℝ

def stressEdgeIncident {n : ℕ} (e : StressEdge n) (i : StressVertex n) : Prop :=
  e.1 = i ∨ e.2 = i

def stressEdgeInside {n : ℕ} (K : Finset (StressVertex n))
    (e : StressEdge n) : Prop :=
  e.1 ∈ K ∧ e.2 ∈ K

def signedStress {n : ℕ} (C H : Finset (StressEdge n))
    (α β : StressEdge n → ℝ) (D : ℝ) (e : StressEdge n) : ℝ :=
  (if e ∈ C then α e else 0) -
    (if e ∈ H then β e / D ^ 2 else 0)

noncomputable def positiveStressEdges {n : ℕ}
    (C H : Finset (StressEdge n)) (α β : StressEdge n → ℝ) (D : ℝ) :
    Finset (StressEdge n) :=
  (planarPairs n).filter (fun e => signedStress C H α β D e ≠ 0)

def positiveStressAdj {n : ℕ} (E : Finset (StressEdge n))
    (i j : StressVertex n) : Prop :=
  i ≠ j ∧ ∃ e ∈ E,
    (e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i)

def positiveStressGraph {n : ℕ} (E : Finset (StressEdge n)) :
    SimpleGraph (StressVertex n) :=
  SimpleGraph.fromRel (positiveStressAdj E)

noncomputable def stressComponentVertices {n : ℕ}
    (G : SimpleGraph (StressVertex n)) (K : G.ConnectedComponent) :
    Finset (StressVertex n) :=
  (Finset.univ : Finset (StressVertex n)).filter
    (fun i => G.connectedComponentMk i = K)

def nontrivialStressComponent {n : ℕ}
    (G : SimpleGraph (StressVertex n)) (K : G.ConnectedComponent) : Prop :=
  2 ≤ (stressComponentVertices G K).card

def stressComponentEdge {n : ℕ}
    (E : Finset (StressEdge n)) (K : Finset (StressVertex n))
    (e : StressEdge n) : Prop :=
  e ∈ E ∧ stressEdgeInside K e

def alternateStressAdj {n : ℕ}
    (E : Finset (StressEdge n)) (removed : StressEdge n)
    (i j : StressVertex n) : Prop :=
  i ≠ j ∧ ∃ e ∈ E, e ≠ removed ∧
    ((e.1 = i ∧ e.2 = j) ∨ (e.1 = j ∧ e.2 = i))

def supportEdgeOnCycle {n : ℕ}
    (E : Finset (StressEdge n)) (K : Finset (StressVertex n))
    (e : StressEdge n) : Prop :=
  stressComponentEdge E K e ∧
    Relation.ReflTransGen
      (fun i j => i ∈ K ∧ j ∈ K ∧ alternateStressAdj E e i j)
      e.1 e.2

def stressDegree {n : ℕ} (E : Finset (StressEdge n))
    (i : StressVertex n) : ℕ :=
  ((Finset.univ : Finset (StressVertex n)).filter
    (fun j => positiveStressAdj E i j)).card

def componentContactEdges {n : ℕ}
    (C E : Finset (StressEdge n)) (K : Finset (StressVertex n)) :
    Finset (StressEdge n) :=
  C.filter (fun e => e ∈ E ∧ stressEdgeInside K e)

def componentDiameterEdges {n : ℕ}
    (H E : Finset (StressEdge n)) (K : Finset (StressVertex n)) :
    Finset (StressEdge n) :=
  H.filter (fun e => e ∈ E ∧ stressEdgeInside K e)

def stressOuter (w : StressPlane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => w i * w j

def componentContactMass {n : ℕ}
    (C E : Finset (StressEdge n)) (K : Finset (StressVertex n))
    (α : StressEdge n → ℝ) : ℝ :=
  ∑ e ∈ componentContactEdges C E K, α e

def componentDiameterMass {n : ℕ}
    (H E : Finset (StressEdge n)) (K : Finset (StressVertex n))
    (β : StressEdge n → ℝ) : ℝ :=
  ∑ e ∈ componentDiameterEdges H E K, β e

def componentContactMoment {n : ℕ}
    (X : StressVertex n → StressPlane)
    (C E : Finset (StressEdge n)) (K : Finset (StressVertex n))
    (α : StressEdge n → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ e ∈ componentContactEdges C E K,
    α e • stressOuter (X e.1 - X e.2)

def componentDiameterMoment {n : ℕ}
    (X : StressVertex n → StressPlane)
    (H E : Finset (StressEdge n)) (K : Finset (StressVertex n))
    (β : StressEdge n → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ e ∈ componentDiameterEdges H E K,
    β e • stressOuter (X e.1 - X e.2)

def stressComponentsPartition {n : ℕ}
    (E : Finset (StressEdge n))
    (G : SimpleGraph (StressVertex n)) : Prop :=
  (∀ e ∈ E, ∃! K : G.ConnectedComponent,
    stressEdgeInside (stressComponentVertices G K) e) ∧
  (∀ K L : G.ConnectedComponent, K ≠ L →
    Disjoint (stressComponentVertices G K) (stressComponentVertices G L))

def stressSupportIsExact {n : ℕ}
    (C H E : Finset (StressEdge n))
    (α β : StressEdge n → ℝ) (D : ℝ) : Prop :=
  ∀ e ∈ planarPairs n,
    e ∈ E ↔ signedStress C H α β D e ≠ 0

/-- The nonzero signed-stress support of a balanced closest/farthest KKT
certificate splits into nontrivial bridgeless mixed components.  Component
masses and moments use the contact and diameter support carriers separately. -/
def positiveKKTStressComponents_claim33740 : Prop :=
  ∀ (n : ℕ) (X : StressVertex n → StressPlane)
    (α β : StressEdge n → ℝ),
    2 ≤ n → planarDistinct X → planarPairMin X = 1 →
    balancedStresses X α β →
      let C := planarClosestPairs X
      let H := planarFarthestPairs X
      let D := planarDiameter X
      let E := positiveStressEdges C H α β D
      let G := positiveStressGraph E
      stressSupportIsExact C H E α β D ∧
        stressComponentsPartition E G ∧
        (∀ K : G.ConnectedComponent,
          nontrivialStressComponent G K →
            (∀ e ∈ E,
              stressEdgeInside (stressComponentVertices G K) e →
                supportEdgeOnCycle E (stressComponentVertices G K) e) ∧
            (∀ i ∈ stressComponentVertices G K, 2 ≤ stressDegree E i) ∧
            (componentContactEdges C E (stressComponentVertices G K)).Nonempty ∧
            (componentDiameterEdges H E (stressComponentVertices G K)).Nonempty ∧
            componentContactMass C E (stressComponentVertices G K) α =
              componentDiameterMass H E (stressComponentVertices G K) β ∧
            componentContactMoment X C E (stressComponentVertices G K) α =
              (1 / D ^ 2) •
                componentDiameterMoment X H E (stressComponentVertices G K) β)

end
end MathlibPlus.Open.ResearchFormalization.R1853
