import MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

namespace MathlibPlus.Open.ResearchFormalization.BatchR1853

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalizationBatch_01a001bb_b98e_7f3f_a02c_7ec8b381d120

noncomputable section

abbrev Vec2 := Fin 2 → ℝ

def balancedStresses {n : ℕ} (X : Fin n → Vec2)
    (α β : Fin n × Fin n → ℝ) : Prop :=
  probabilityWeight (planarClosestPairs X) α ∧
    probabilityWeight (planarFarthestPairs X) β ∧
    ∀ w : Fin n → Vec2,
      (∑ e ∈ planarPairs n, α e * planarVelocityValue X w e) =
        ∑ e ∈ planarPairs n, β e * planarVelocityValue X w e

/-- The signed force contributed by an edge at one of its incident vertices;
nonincident vertices contribute zero. -/
def incidentForce {n : ℕ} (X : Fin n → Vec2) (e : Fin n × Fin n)
    (i : Fin n) : Vec2 :=
  if i = e.1 then X e.1 - X e.2
  else if i = e.2 then X e.2 - X e.1
  else 0

def weightedForce {n : ℕ} (X : Fin n → Vec2)
    (a : Fin n × Fin n → ℝ) (i : Fin n) : Vec2 :=
  ∑ e : Fin n × Fin n, a e • incidentForce X e i

def outerProduct (u : Vec2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => u i * u j

def weightedMoment {n : ℕ} (X : Fin n → Vec2)
    (a : Fin n × Fin n → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ e : Fin n × Fin n, a e • outerProduct (X e.1 - X e.2)

/-- Claim 33702: normalized balanced closest/farthest stresses give both the
vertex equilibrium and the equal weighted second-moment identity. -/
def vertexEquilibriumAndSecondMoment_claim33702 : Prop :=
  ∀ (n : ℕ) (X : Fin n → Vec2) (α β : Fin n × Fin n → ℝ),
    2 ≤ n → planarDistinct X → planarPairMin X = 1 →
      balancedStresses X α β →
      (∀ i : Fin n,
        weightedForce X α i =
          (1 / (planarDiameter X) ^ 2) • weightedForce X β i) ∧
      weightedMoment X α =
        (1 / (planarDiameter X) ^ 2) • weightedMoment X β

/-- The contact cut flux is oriented from the member of `S` to its complement,
including the reverse orientation when the larger endpoint is in `S`. -/
def contactCutFlux {n : ℕ} (X : Fin n → Vec2)
    (α : Fin n × Fin n → ℝ) (S : Finset (Fin n)) : Vec2 :=
  ∑ e : Fin n × Fin n,
    if e.1 ∈ S ∧ e.2 ∉ S then
      α e • (X e.1 - X e.2)
    else if e.2 ∈ S ∧ e.1 ∉ S then
      α e • (X e.2 - X e.1)
    else 0

def diameterEndpointFlux {n : ℕ} (X : Fin n → Vec2)
    (β : Fin n × Fin n → ℝ) (S : Finset (Fin n)) : Vec2 :=
  ∑ i ∈ S, ∑ e : Fin n × Fin n, β e • incidentForce X e i

def noDiameterEndpoint {n : ℕ} (X : Fin n → Vec2)
    (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ e : Fin n × Fin n, e ∈ planarFarthestPairs X →
    ¬ (i = e.1 ∨ i = e.2)

/-- Claim 33729: summing the correctly oriented vertex equilibrium over any
vertex set gives the exact contact cut-flux identity, and a set with no
farthest endpoint has zero right-hand endpoint sum. -/
def exactCutFluxIdentity_claim33729 : Prop :=
  ∀ (n : ℕ) (X : Fin n → Vec2) (α β : Fin n × Fin n → ℝ)
    (S : Finset (Fin n)),
    2 ≤ n → planarDistinct X → planarPairMin X = 1 →
      balancedStresses X α β →
      (∀ i : Fin n,
        weightedForce X α i =
          (1 / (planarDiameter X) ^ 2) • weightedForce X β i) →
      contactCutFlux X α S =
          (1 / (planarDiameter X) ^ 2) • diameterEndpointFlux X β S ∧
        (noDiameterEndpoint X S → diameterEndpointFlux X β S = 0)

abbrev GridVertex (p q : ℕ) := Fin (p + 1) × Fin (q + 1)
abbrev GridPair (p q : ℕ) := GridVertex p q × GridVertex p q

noncomputable def gridPairs (p q : ℕ) : Finset (GridPair p q) := by
  classical
  exact (Finset.univ.product Finset.univ).filter (fun e => e.1 < e.2)

def gridPoint {p q : ℕ} (u v : Vec2)
    (a : GridVertex p q) : Vec2 :=
  (a.1.val : ℝ) • u + (a.2.val : ℝ) • v

def gridDifference {p q : ℕ} (u v : Vec2)
    (e : GridPair p q) : Vec2 :=
  gridPoint u v e.1 - gridPoint u v e.2

def gridNormSq (w : Vec2) : ℝ := planarDot w w

def gridHorizontalAdj {p q : ℕ}
    (a b : GridVertex p q) : Prop :=
  a.2 = b.2 ∧
    (a.1.val + 1 = b.1.val ∨ b.1.val + 1 = a.1.val)

def gridVerticalAdj {p q : ℕ}
    (a b : GridVertex p q) : Prop :=
  a.1 = b.1 ∧
    (a.2.val + 1 = b.2.val ∨ b.2.val + 1 = a.2.val)
def gridAdj {p q : ℕ} (a b : GridVertex p q) : Prop :=
  gridHorizontalAdj a b ∨ gridVerticalAdj a b

def gridUnitPair {p q : ℕ} (u v : Vec2)
    (e : GridPair p q) : Prop :=
  e ∈ gridPairs p q ∧ gridNormSq (gridDifference u v e) = 1

def gridDiameterPair {p q : ℕ} (u v : Vec2) (Dsq : ℝ)
    (e : GridPair p q) : Prop :=
  e ∈ gridPairs p q ∧ gridNormSq (gridDifference u v e) = Dsq

def unorderedGridPair {p q : ℕ} (e : GridPair p q)
    (a b : GridVertex p q) : Prop :=
  (e.1 = a ∧ e.2 = b) ∨ (e.1 = b ∧ e.2 = a)

def corner00 (p q : ℕ) : GridVertex p q :=
  (⟨0, Nat.zero_lt_succ p⟩, ⟨0, Nat.zero_lt_succ q⟩)
def cornerPQ (p q : ℕ) : GridVertex p q :=
  (⟨p, Nat.lt_succ_self p⟩, ⟨q, Nat.lt_succ_self q⟩)
def corner0Q (p q : ℕ) : GridVertex p q :=
  (⟨0, Nat.zero_lt_succ p⟩, ⟨q, Nat.lt_succ_self q⟩)
def cornerP0 (p q : ℕ) : GridVertex p q :=
  (⟨p, Nat.lt_succ_self p⟩, ⟨0, Nat.zero_lt_succ q⟩)
def mainCornerPair {p q : ℕ} (e : GridPair p q) : Prop :=
  unorderedGridPair e (corner00 p q) (cornerPQ p q)
def otherCornerPair {p q : ℕ} (e : GridPair p q) : Prop :=
  unorderedGridPair e (corner0Q p q) (cornerP0 p q)
def cornerDiameterPair {p q : ℕ} (e : GridPair p q) : Prop :=
  mainCornerPair e ∨ otherCornerPair e

def gridTriangleFree (p q : ℕ) : Prop :=
  ∀ a b c : GridVertex p q,
    a ≠ b → a ≠ c → b ≠ c →
      ¬ (gridAdj a b ∧ gridAdj b c ∧ gridAdj a c)

def gridIncidentForce {p q : ℕ} (u v : Vec2)
    (e : GridPair p q) (a : GridVertex p q) : Vec2 :=
  if a = e.1 then gridDifference u v e
  else if a = e.2 then -gridDifference u v e
  else 0

def gridOuterProduct (w : Vec2) : Matrix (Fin 2) (Fin 2) ℝ :=
  outerProduct w

def gridProbability (p q : ℕ) (w : GridPair p q → ℝ) : Prop :=
  (∀ e, 0 ≤ w e) ∧
    (∑ e ∈ gridPairs p q, w e) = 1 ∧
    (∀ e, e ∉ gridPairs p q → w e = 0)

def gridBalancedStress (p q : ℕ) (u v : Vec2) (Dsq : ℝ)
    (α β : GridPair p q → ℝ) : Prop :=
  0 < Dsq ∧
    gridProbability p q α ∧ gridProbability p q β ∧
    (∀ e, e ∈ gridPairs p q →
      ((¬ gridUnitPair u v e → α e = 0) ∧
        (¬ gridDiameterPair u v Dsq e → β e = 0))) ∧
    (∀ a : GridVertex p q,
      ∑ e ∈ gridPairs p q, α e • gridIncidentForce u v e a =
        (1 / Dsq) •
          ∑ e ∈ gridPairs p q, β e • gridIncidentForce u v e a) ∧
    (∑ e ∈ gridPairs p q, α e • gridOuterProduct (gridDifference u v e)) =
      (1 / Dsq) •
        ∑ e ∈ gridPairs p q, β e • gridOuterProduct (gridDifference u v e)

def gridKKTFeasible (p q : ℕ) (u v : Vec2) (Dsq : ℝ) : Prop :=
  ∃ α β : GridPair p q → ℝ,
    gridBalancedStress p q u v Dsq α β

def gridBoundaryHorizontal {p q : ℕ} (e : GridPair p q) : Prop :=
  gridHorizontalAdj e.1 e.2 ∧
    (e.1.2.val = 0 ∨ e.1.2.val = q)
def gridBoundaryVertical {p q : ℕ} (e : GridPair p q) : Prop :=
  gridVerticalAdj e.1 e.2 ∧
    (e.1.1.val = 0 ∨ e.1.1.val = p)

noncomputable def boundaryAlpha (p q : ℕ) (Dsq : ℝ)
    (e : GridPair p q) : ℝ := by
  classical
  exact if gridBoundaryHorizontal e then (p : ℝ) / (2 * Dsq)
    else if gridBoundaryVertical e then (q : ℝ) / (2 * Dsq)
    else 0

noncomputable def cornerBeta {p q : ℕ} (e : GridPair p q) : ℝ := by
  classical
  exact if cornerDiameterPair e then (1 / 2 : ℝ) else 0

def gridDisplacement (a b : ℤ) (u v : Vec2) : Vec2 :=
  (a : ℝ) • u + (b : ℝ) • v

def gridDifferenceFormula (u v : Vec2) : Prop :=
  ∀ a b : ℤ,
    gridNormSq (gridDisplacement a b u v) =
      (a : ℝ) ^ 2 + (b : ℝ) ^ 2 +
        2 * (a : ℝ) * (b : ℝ) * planarDot u v

def gridDiameterSq (p q : ℕ) (u v : Vec2) : ℝ :=
  (p : ℝ) ^ 2 + (q : ℝ) ^ 2 +
    2 * (p : ℝ) * (q : ℝ) * planarDot u v

/-- Claim 33732: the complete unit-grid contact/diameter classification and
exact iff KKT stress statement, including the orthogonal boundary weights. -/
def orthogonalParallelogramGrid_claim33732 : Prop :=
  ∀ (p q : ℕ), 1 ≤ p → 1 ≤ q →
    ∀ (u v : Vec2),
      gridNormSq u = 1 → gridNormSq v = 1 →
      0 ≤ planarDot u v → planarDot u v < 1 / 2 →
      gridDifferenceFormula u v ∧
      gridTriangleFree p q ∧
      (∀ e : GridPair p q, gridUnitPair u v e ↔
        (e ∈ gridPairs p q ∧ gridAdj e.1 e.2)) ∧
      (planarDot u v > 0 →
        ∀ e : GridPair p q,
          gridDiameterPair u v (gridDiameterSq p q u v) e ↔
            mainCornerPair e) ∧
      (planarDot u v = 0 →
        ∀ e : GridPair p q,
          gridDiameterPair u v (gridDiameterSq p q u v) e ↔
            cornerDiameterPair e) ∧
      (gridKKTFeasible p q u v (gridDiameterSq p q u v) ↔
        planarDot u v = 0) ∧
      (planarDot u v = 0 →
        gridBalancedStress p q u v (gridDiameterSq p q u v)
          (boundaryAlpha p q (gridDiameterSq p q u v)) cornerBeta)

end
end MathlibPlus.Open.ResearchFormalization.BatchR1853
