import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a000fb

noncomputable section

/-! A direct finite model for the two-component Boolean channel in R-4219. -/

abbrev Observation53335 := Bool × Bool

def sign53335 (b : Bool) : ℚ := if b then 1 else -1

def componentA53335 (o : Observation53335) : ℚ :=
  if o.2 = false then sign53335 o.1 else 1

def componentB53335 (o : Observation53335) : ℚ := sign53335 o.1

def mixtureMean53335 (o : Observation53335) : ℚ :=
  (1 / 3 : ℚ) * componentA53335 o + (2 / 3 : ℚ) * componentB53335 o

def conditionalPlusProbability53335 (o : Observation53335) : ℚ :=
  (1 + mixtureMean53335 o) / 2

def conditionalY53335 (o : Observation53335) (y : Bool) : ℚ :=
  if y then conditionalPlusProbability53335 o
  else 1 - conditionalPlusProbability53335 o

def displayedCostA53335 (o : Observation53335) : ℚ :=
  if o.2 = false then 2 else 1

def displayedCostB53335 (_o : Observation53335) : ℚ := 1

def uniformObservation53335 (_o : Observation53335) : ℚ :=
  1 / 4

def thetaProbabilityA53335 : ℚ := 1 / 3

def thetaProbabilityB53335 : ℚ := 2 / 3

def claim_53335 : Prop :=
  (∀ o : Observation53335, uniformObservation53335 o = (1 / 4 : ℚ)) ∧
    (Finset.sum Finset.univ uniformObservation53335 = 1) ∧
    thetaProbabilityA53335 = (1 / 3 : ℚ) ∧
    thetaProbabilityB53335 = (2 / 3 : ℚ) ∧
    (thetaProbabilityA53335 + thetaProbabilityB53335 = 1) ∧
    ((1 / 3 : ℚ) + (2 / 3 : ℚ) = 1) ∧
    (∀ o : Observation53335,
      conditionalY53335 o true = (1 + mixtureMean53335 o) / 2 ∧
        conditionalY53335 o false = (1 - mixtureMean53335 o) / 2) ∧
    ((Finset.sum Finset.univ
        (fun o => uniformObservation53335 o * displayedCostA53335 o)) =
      (3 / 2 : ℚ)) ∧
    ((Finset.sum Finset.univ
        (fun o => uniformObservation53335 o * displayedCostB53335 o)) =
      (1 : ℚ))

/-! Finite undirected edge sets and their component-size forest polynomial. -/

def edgeRelation53363 {n : ℕ} (E : Finset (Fin n × Fin n)) : Fin n → Fin n → Prop :=
  fun u v => (u, v) ∈ E ∨ (v, u) ∈ E

def reachable53363 {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (edgeRelation53363 E) u v

def treeEdges53363 {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  0 < n ∧
    (∀ e ∈ E, e.1 ≠ e.2 ∧ (e.2, e.1) ∉ E) ∧
    (∀ u v : Fin n, reachable53363 E u v) ∧
    E.card = n - 1

def component53363 {n : ℕ} (E : Finset (Fin n × Fin n)) (V : Finset (Fin n))
    (u : Fin n) : Finset (Fin n) := by
  classical
  exact V.filter (fun v => reachable53363 E u v)

def representatives53363 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact V.filter (fun u => ∀ v ∈ V, reachable53363 E u v → u.val ≤ v.val)

def componentSize53363 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) (u : Fin n) : ℕ :=
  (component53363 E V u).card

def forestPolynomial53363 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) : MvPolynomial ℕ ℤ := by
  classical
  let E₀ := E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ V)
  exact Finset.sum E₀.powerset (fun A =>
    Finset.prod (representatives53363 A V)
      (fun u => MvPolynomial.X (componentSize53363 A V u)))

def U53363 {n : ℕ} (E : Finset (Fin n × Fin n)) : MvPolynomial ℕ ℤ :=
  forestPolynomial53363 E Finset.univ

def M53363 {n : ℕ} (E : Finset (Fin n × Fin n)) : MvPolynomial ℕ ℤ :=
  MvPolynomial.pderiv 1 (U53363 E)

def claim_53363 : Prop := by
  classical
  exact ∀ (n : ℕ) (E : Finset (Fin n × Fin n)), treeEdges53363 E →
    U53363 E = forestPolynomial53363 E Finset.univ ∧
      M53363 E = MvPolynomial.pderiv 1 (U53363 E)

def connectedSubset53346 {n : ℕ} (E : Finset (Fin n × Fin n))
    (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧
    ∀ u ∈ C, ∀ v ∈ C,
      Relation.ReflTransGen
        (fun a b => a ∈ C ∧ b ∈ C ∧ edgeRelation53363 E a b) u v

def claim_53346 : Prop := by
  classical
  exact   ∀ (n : ℕ) (E : Finset (Fin n × Fin n)), treeEdges53363 E →
    ∀ k : ℕ, 1 ≤ k →
      MvPolynomial.pderiv k (U53363 E) =
        Finset.sum
          ((Finset.univ : Finset (Finset (Fin n))).filter
            (fun C => C.card = k ∧ connectedSubset53346 E C))
          (fun C => forestPolynomial53363 E (Finset.univ \ C))

/-! The generalized-degree polynomial model and the displayed order-eleven pair. -/

def xIndex53354 {m : ℕ} (i : Fin m) : Fin (2 * m + 1) :=
  ⟨i.val, by omega⟩

def zIndex53354 {m : ℕ} (i : Fin m) : Fin (2 * m + 1) :=
  ⟨m + i.val, by omega⟩

def yIndex53354 (m : ℕ) : Fin (2 * m + 1) :=
  ⟨2 * m, by omega⟩

def xVar53354 {m : ℕ} (i : Fin m) : MvPolynomial (Fin (2 * m + 1)) ℤ :=
  MvPolynomial.X (xIndex53354 i)

def zVar53354 {m : ℕ} (i : Fin m) : MvPolynomial (Fin (2 * m + 1)) ℤ :=
  MvPolynomial.X (zIndex53354 i)

def yVar53354 (m : ℕ) : MvPolynomial (Fin (2 * m + 1)) ℤ :=
  MvPolynomial.X (yIndex53354 m)

def positiveColor53354 {m : ℕ} (i : Fin m) : Fin (m + 1) :=
  ⟨i.val + 1, by omega⟩

def vertexWeight53354 (m : ℕ) (c : Fin (m + 1)) :
    MvPolynomial (Fin (2 * m + 1)) ℤ := by
  by_cases h : c.val = 0
  · exact 1
  · exact MvPolynomial.X (xIndex53354 ⟨c.val - 1, by omega⟩)

def edgeWeight53354 (m : ℕ) (a b : Fin (m + 1)) :
    MvPolynomial (Fin (2 * m + 1)) ℤ := by
  by_cases h00 : a.val = 0 ∧ b.val = 0
  · exact 1
  · by_cases hab : a = b
    · by_cases ha0 : a.val = 0
      · exact 1
      · exact MvPolynomial.X (zIndex53354 ⟨a.val - 1, by omega⟩)
    · exact yVar53354 m

def generalizedDegreePolynomial53354 (m n : ℕ)
    (E : Finset (Fin n × Fin n)) : MvPolynomial (Fin (2 * m + 1)) ℤ :=
  Finset.sum Finset.univ (fun c : (Fin n → Fin (m + 1)) =>
    (Finset.prod Finset.univ (fun v : Fin n => vertexWeight53354 m (c v))) *
      (Finset.prod E (fun e => edgeWeight53354 m (c e.1) (c e.2))))

def edgesA53355 : Finset (Fin 11 × Fin 11) :=
  {(0, 1), (0, 7), (1, 2), (1, 5), (1, 6),
    (2, 3), (2, 4), (7, 8), (7, 10), (8, 9)}

def edgesB53355 : Finset (Fin 11 × Fin 11) :=
  {(0, 1), (0, 5), (0, 10), (1, 2), (2, 3),
    (2, 4), (5, 6), (5, 8), (5, 9), (6, 7)}

def claim_53354 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    Fintype.card (Fin (m + 1)) = m + 1 ∧
      (∀ i : Fin m,
        vertexWeight53354 m (positiveColor53354 i) = xVar53354 i) ∧
      edgeWeight53354 m 0 0 = 1 ∧
      (∀ i : Fin m,
        edgeWeight53354 m (positiveColor53354 i) (positiveColor53354 i) = zVar53354 i) ∧
      (∀ a b : Fin (m + 1), a ≠ b → edgeWeight53354 m a b = yVar53354 m) ∧
      (∀ n : ℕ, ∀ E : Finset (Fin n × Fin n),
        generalizedDegreePolynomial53354 m n E =
          Finset.sum Finset.univ (fun c : (Fin n → Fin (m + 1)) =>
            (Finset.prod Finset.univ (fun v : Fin n => vertexWeight53354 m (c v))) *
              (Finset.prod E (fun e => edgeWeight53354 m (c e.1) (c e.2)))))

def claim_53356 : Prop :=
  generalizedDegreePolynomial53354 1 11 edgesA53355 =
    generalizedDegreePolynomial53354 1 11 edgesB53355

abbrev Poly53357 := MvPolynomial (Fin 5) ℤ

def x1_53357 : Poly53357 := MvPolynomial.X 0

def x2_53357 : Poly53357 := MvPolynomial.X 1

def z1_53357 : Poly53357 := MvPolynomial.X 2

def z2_53357 : Poly53357 := MvPolynomial.X 3

def y_53357 : Poly53357 := MvPolynomial.X 4

def lambda0_53357 : Poly53357 := 1 + y_53357 * (x1_53357 + x2_53357)

def lambda1_53357 : Poly53357 := y_53357 + x1_53357 * z1_53357 + x2_53357 * y_53357

def lambda2_53357 : Poly53357 := y_53357 + x1_53357 * y_53357 + x2_53357 * z2_53357

def rho_53357 : Poly53357 :=
  1 + y_53357 + x1_53357 * (y_53357 + z1_53357) +
    x2_53357 * (y_53357 + z2_53357)

def claim_53357 : Prop :=
  generalizedDegreePolynomial53354 2 11 edgesA53355 -
      generalizedDegreePolynomial53354 2 11 edgesB53355 =
    -x1_53357 * x2_53357 * y_53357 ^ 2 * rho_53357 ^ 2 *
      ((lambda0_53357 - lambda1_53357) ^ 2 *
        (lambda0_53357 - lambda2_53357) ^ 2 *
        (lambda1_53357 - lambda2_53357) ^ 2) ∧
    x1_53357 ≠ 0 ∧ x2_53357 ≠ 0 ∧ y_53357 ≠ 0 ∧ rho_53357 ≠ 0 ∧
      lambda0_53357 - lambda1_53357 ≠ 0 ∧
      lambda0_53357 - lambda2_53357 ≠ 0 ∧
      lambda1_53357 - lambda2_53357 ≠ 0 ∧
      generalizedDegreePolynomial53354 2 11 edgesA53355 -
          generalizedDegreePolynomial53354 2 11 edgesB53355 ≠ 0

def sigmaVariable53358 (m : ℕ) (i : Fin (2 * m + 1)) : Poly53357 := by
  by_cases hx : i.val < m
  · by_cases hsmall : i.val < 2
    · exact MvPolynomial.X ⟨i.val, by omega⟩
    · exact 0
  · by_cases hy : i.val = 2 * m
    · exact MvPolynomial.X 4
    · by_cases hsmall : i.val - m < 2
      · exact MvPolynomial.X ⟨i.val - m + 2, by omega⟩
      · exact 0

def sigma53358 (m : ℕ) :
    MvPolynomial (Fin (2 * m + 1)) ℤ →+* Poly53357 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (sigmaVariable53358 m)

def targetX53358 {m : ℕ} (i : Fin m) : Poly53357 :=
  MvPolynomial.X ⟨min i.val 4, by omega⟩

def targetZ53358 {m : ℕ} (i : Fin m) : Poly53357 :=
  MvPolynomial.X ⟨min (i.val + 2) 4, by omega⟩

def claim_53358 : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∀ i : Fin m, i.val < 2 →
      sigma53358 m (MvPolynomial.X (xIndex53354 i)) = targetX53358 i) ∧
    (∀ i : Fin m, i.val < 2 →
      sigma53358 m (MvPolynomial.X (zIndex53354 i)) = targetZ53358 i) ∧
    sigma53358 m (MvPolynomial.X (yIndex53354 m)) = MvPolynomial.X 4 ∧
    (∀ i : Fin m, 2 ≤ i.val →
      sigma53358 m (MvPolynomial.X (xIndex53354 i)) = 0 ∧
        sigma53358 m (MvPolynomial.X (zIndex53354 i)) = 0) ∧
    (∀ n : ℕ, ∀ E : Finset (Fin n × Fin n),
      sigma53358 m (generalizedDegreePolynomial53354 m n E) =
        generalizedDegreePolynomial53354 2 n E)

def claim_53359 : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    sigma53358 m
        (generalizedDegreePolynomial53354 m 11 edgesA53355 -
          generalizedDegreePolynomial53354 m 11 edgesB53355) =
        generalizedDegreePolynomial53354 2 11 edgesA53355 -
          generalizedDegreePolynomial53354 2 11 edgesB53355 ∧
      generalizedDegreePolynomial53354 m 11 edgesA53355 ≠
        generalizedDegreePolynomial53354 m 11 edgesB53355

/-! The order-two legal-centroid boundary and the finite injectivity assertion. -/

def edgeRelation53366 {n : ℕ} (E : Finset (Fin n × Fin n)) : Fin n → Fin n → Prop :=
  fun u v => u ≠ v ∧ ((u, v) ∈ E ∨ (v, u) ∈ E)

def deletedEdgeRelation53366 {n : ℕ} (E : Finset (Fin n × Fin n))
    (c : Fin n) (u v : Fin n) : Prop :=
  u ≠ c ∧ v ≠ c ∧ edgeRelation53366 E u v

def deletedReachable53366 {n : ℕ} (E : Finset (Fin n × Fin n))
    (c u v : Fin n) : Prop :=
  Relation.ReflTransGen (deletedEdgeRelation53366 E c) u v

def deletedComponent53366 {n : ℕ} (E : Finset (Fin n × Fin n))
    (c v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => deletedReachable53366 E c v w)

def centroid53366 {n : ℕ} (E : Finset (Fin n × Fin n)) (c : Fin n) : Prop :=
  ∀ v : Fin n, v ≠ c → 2 * (deletedComponent53366 E c v).card ≤ n

def legal53366 {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∃! c : Fin n,
    centroid53366 E c ∧
      ∀ v : Fin n, v ≠ c → 2 * (deletedComponent53366 E c v).card < n

def claim_53366 : Prop :=
  ∀ E : Finset (Fin 2 × Fin 2), treeEdges53363 E → ¬ legal53366 E

def graphIso53367 {n : ℕ} (E F : Finset (Fin n × Fin n)) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
    ((u, v) ∈ E ∨ (v, u) ∈ E) ↔
      ((e u, e v) ∈ F ∨ (e v, e u) ∈ F)

def claim_53367 : Prop :=
  ∀ n : ℕ, n ≤ 16 →
    ∀ E F : Finset (Fin n × Fin n),
      treeEdges53363 E → treeEdges53363 F →
      legal53366 E → legal53366 F → ¬ graphIso53367 E F →
      M53363 E ≠ M53363 F

end

end MathlibPlus.Open.ResearchFormalizationBatch_01a000fb
