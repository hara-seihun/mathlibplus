import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch_53368

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-! The explicit finite edge-set carrier and component-size polynomial. -/

def edgeRelation53368 {n : ℕ} (E : Finset (Fin n × Fin n)) : Fin n → Fin n → Prop :=
  fun u v => (u, v) ∈ E ∨ (v, u) ∈ E

def reachable53368 {n : ℕ} (E : Finset (Fin n × Fin n)) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (edgeRelation53368 E) u v

def treeEdges53368 {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  0 < n ∧
    (∀ e ∈ E, e.1 ≠ e.2 ∧ (e.2, e.1) ∉ E) ∧
    (∀ u v : Fin n, reachable53368 E u v) ∧
    E.card = n - 1

def component53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) (u : Fin n) : Finset (Fin n) := by
  classical
  exact V.filter (fun v => reachable53368 E u v)

def representatives53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact V.filter (fun u => ∀ v ∈ V, reachable53368 E u v → u.val ≤ v.val)

def componentSize53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) (u : Fin n) : ℕ :=
  (component53368 E V u).card

def forestPolynomial53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (V : Finset (Fin n)) : MvPolynomial ℕ ℤ := by
  classical
  let E₀ := E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ V)
  exact Finset.sum E₀.powerset (fun A =>
    Finset.prod (representatives53368 A V)
      (fun u => MvPolynomial.X (componentSize53368 A V u)))

def U53368 {n : ℕ} (E : Finset (Fin n × Fin n)) : MvPolynomial ℕ ℤ :=
  forestPolynomial53368 E Finset.univ

def M53368 {n : ℕ} (E : Finset (Fin n × Fin n)) : MvPolynomial ℕ ℤ :=
  MvPolynomial.pderiv 1 (U53368 E)

/-! The legal unique-centroid class and the graph-isomorphism relation. -/

def deletedEdgeRelation53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (c : Fin n) (u v : Fin n) : Prop :=
  u ≠ c ∧ v ≠ c ∧ edgeRelation53368 E u v

def deletedReachable53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (c u v : Fin n) : Prop :=
  Relation.ReflTransGen (deletedEdgeRelation53368 E c) u v

def deletedComponent53368 {n : ℕ} (E : Finset (Fin n × Fin n))
    (c v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun w => deletedReachable53368 E c v w)

def centroid53368 {n : ℕ} (E : Finset (Fin n × Fin n)) (c : Fin n) : Prop :=
  ∀ v : Fin n, v ≠ c → 2 * (deletedComponent53368 E c v).card ≤ n

def legal53368 {n : ℕ} (E : Finset (Fin n × Fin n)) : Prop :=
  ∃! c : Fin n,
    centroid53368 E c ∧
      ∀ v : Fin n, v ≠ c → 2 * (deletedComponent53368 E c v).card < n

def graphIso53368 {n : ℕ} (E F : Finset (Fin n × Fin n)) : Prop :=
  ∃ e : Fin n ≃ Fin n, ∀ u v : Fin n,
    ((u, v) ∈ E ∨ (v, u) ∈ E) ↔
      ((e u, e v) ∈ F ∨ (e v, e u) ∈ F)

abbrev TreeEdgeSet53368 (n : ℕ) :=
  {E : Finset (Fin n × Fin n) // treeEdges53368 E}

def treeIso53368 {n : ℕ} (E F : TreeEdgeSet53368 n) : Prop :=
  graphIso53368 E.1 F.1

def treeSetoid53368 (n : ℕ) : Setoid (TreeEdgeSet53368 n) where
  r := treeIso53368
  iseqv := by
    constructor
    · intro E
      refine ⟨Equiv.refl _, ?_⟩
      intro u v
      simp
    · intro E F h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro u v
      simpa using (h (e.symm u) (e.symm v)).symm
    · intro E F G hEF hFG
      rcases hEF with ⟨e, hEF⟩
      rcases hFG with ⟨f, hFG⟩
      refine ⟨e.trans f, ?_⟩
      intro u v
      exact (hEF u v).trans (hFG (e u) (e v))

abbrev TreeClass53368 (n : ℕ) := Quotient (treeSetoid53368 n)

noncomputable def treeCount53368 (n : ℕ) : ℕ :=
  Nat.card (TreeClass53368 n)

abbrev LegalTreeEdgeSet53368 (n : ℕ) :=
  {E : Finset (Fin n × Fin n) // treeEdges53368 E ∧ legal53368 E}

def legalTreeIso53368 {n : ℕ} (E F : LegalTreeEdgeSet53368 n) : Prop :=
  graphIso53368 E.1 F.1

def legalTreeSetoid53368 (n : ℕ) : Setoid (LegalTreeEdgeSet53368 n) where
  r := legalTreeIso53368
  iseqv := by
    constructor
    · intro E
      refine ⟨Equiv.refl _, ?_⟩
      intro u v
      simp
    · intro E F h
      rcases h with ⟨e, h⟩
      refine ⟨e.symm, ?_⟩
      intro u v
      simpa using (h (e.symm u) (e.symm v)).symm
    · intro E F G hEF hFG
      rcases hEF with ⟨e, hEF⟩
      rcases hFG with ⟨f, hFG⟩
      refine ⟨e.trans f, ?_⟩
      intro u v
      exact (hEF u v).trans (hFG (e u) (e v))

abbrev LegalTreeClass53368 (n : ℕ) :=
  Quotient (legalTreeSetoid53368 n)

noncomputable def legalTreeCount53368 (n : ℕ) : ℕ :=
  Nat.card (LegalTreeClass53368 n)

/-- The finite carrier of complete `M` signatures represented by legal trees. -/
def legalEdgeSets53368 (n : ℕ) : Finset (Finset (Fin n × Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
    (fun E => treeEdges53368 E ∧ legal53368 E)

def signatureValues53368 (n : ℕ) : Finset (MvPolynomial ℕ ℤ) :=
  (legalEdgeSets53368 n).image M53368

noncomputable def signatureCount53368 (n : ℕ) : ℕ :=
  (signatureValues53368 n).card

def censusRow53368 (n all legal signatures : ℕ) : Prop :=
  treeCount53368 n = all ∧
    legalTreeCount53368 n = legal ∧
    signatureCount53368 n = signatures

def censusTable53368 : Prop :=
  censusRow53368 2 1 0 0 ∧
  censusRow53368 3 1 1 1 ∧
  censusRow53368 4 2 1 1 ∧
  censusRow53368 5 3 3 3 ∧
  censusRow53368 6 6 3 3 ∧
  censusRow53368 7 11 11 11 ∧
  censusRow53368 8 23 13 13 ∧
  censusRow53368 9 47 47 47 ∧
  censusRow53368 10 106 61 61 ∧
  censusRow53368 11 235 235 235 ∧
  censusRow53368 12 551 341 341 ∧
  censusRow53368 13 1301 1301 1301 ∧
  censusRow53368 14 3159 1983 1983 ∧
  censusRow53368 15 7741 7741 7741 ∧
  censusRow53368 16 19320 12650 12650

def signatureClassesSingleton53368 : Prop :=
  ∀ n : ℕ, n ≤ 16 →
    ∀ E F : Finset (Fin n × Fin n),
      treeEdges53368 E → treeEdges53368 F →
      legal53368 E → legal53368 F →
      M53368 E = M53368 F → graphIso53368 E F

/-- Claim 53368: the exact order-by-order unlabelled tree census, its legal
unique-centroid counts, and singleton complete-signature classes through order
sixteen. -/
def claim_53368 : Prop :=
  censusTable53368 ∧
    (∑ n ∈ Finset.Icc 2 16, legalTreeCount53368 n) = 24391 ∧
    signatureClassesSingleton53368

end

end MathlibPlus.Open.ResearchFormalizationBatch_53368
