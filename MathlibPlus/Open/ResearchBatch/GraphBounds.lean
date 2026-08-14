import Mathlib

namespace MathlibPlus.Open.ResearchBatch.GraphBounds

open scoped BigOperators

noncomputable section

/-- An induced forest witness is a finite vertex set whose induced graph is acyclic. -/
def inducedForest {V : Type*} [Fintype V] (H : SimpleGraph V) (S : Finset V) : Prop :=
  (H.induce (S : Set V)).IsAcyclic

def inducedForestNumber {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.powerset).sup
    (fun S => if inducedForest H S then S.card else 0)

/-- Claim 22433. -/
def claim_22433 {V : Type*} [Fintype V] (H : SimpleGraph V) : Prop :=
  (¬ ∃ S : Finset V, S.card = 5 ∧ inducedForest H S) ↔
    ((∀ S : Finset V, S.card = 5 → ¬ inducedForest H S) ∧
      inducedForestNumber H ≤ 4)

/-- The vertices selected by the one-earlier-neighbor rule. -/
def earlierSelected {V : Type*} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v =>
    (Finset.univ.filter (fun w : V => H.Adj v w ∧ w < v)).card ≤ 1)

/-- Claim 22434. -/
def claim_22434 {V : Type*} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) : Prop :=
  (H.induce (earlierSelected H : Set V)).IsAcyclic

def graphDegree {V : Type*} [Fintype V] (H : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : V => H.Adj v w)).card

def selectedByPermutation {V : Type*} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (σ : Equiv.Perm V) (v : V) : Prop := by
  classical
  exact (Finset.univ.filter (fun w : V => H.Adj v w ∧ σ w < σ v)).card ≤ 1

def selectorProbability {V : Type*} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (v : V) : ℚ := by
  classical
  exact ((Finset.univ.filter (fun σ : Equiv.Perm V =>
      selectedByPermutation H σ v)).card : ℚ) /
    Fintype.card (Equiv.Perm V)

def selectorDegreeProbability (d : ℕ) : ℚ :=
  min 1 ((2 : ℚ) / ((d : ℚ) + 1))

/-- Claim 22435. -/
def claim_22435 {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (H : SimpleGraph V) : Prop :=
  (∀ v : V, selectorProbability H v = selectorDegreeProbability (graphDegree H v)) ∧
    (inducedForestNumber H : ℚ) ≥
      ∑ v : V, selectorDegreeProbability (graphDegree H v)

/-- Claim 22436. -/
def claim_22436 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    (∀ d : ℕ,
      selectorDegreeProbability d ≥
        2 * (2 * (k : ℚ) - 1 - (d : ℚ)) / (k : ℚ) ^ 2) ∧
    (∀ d : ℕ,
      selectorDegreeProbability d ≥
        2 * (2 * (k : ℚ) - (d : ℚ)) / ((k : ℚ) * (k + 1)))

def balancedPart {n : ℕ} (x : Fin n) : Prop :=
  x.val < n / 2

def balancedCliqueGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ (balancedPart x ↔ balancedPart y)
  symm := ⟨fun x y h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

def balancedEdgeTarget (n : ℕ) : ℕ :=
  (n / 2) * (n / 2 - 1) / 2 +
    (n - n / 2) * (n - n / 2 - 1) / 2

def edgeCountOnFin {n : ℕ} (H : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((Finset.univ.product Finset.univ).filter
    (fun p => p.1 < p.2 ∧ H.Adj p.1 p.2)).card

def containsTriangle {V : Type*} (H : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ H.Adj a b ∧ H.Adj a c ∧ H.Adj b c

/-- Claim 22438.  `balancedEdgeTarget` is the integer form of
`ceil (n (n - 2) / 4)`. -/
def claim_22438 (n : ℕ) : Prop :=
  inducedForestNumber (balancedCliqueGraph n) ≤ 4 ∧
    edgeCountOnFin (balancedCliqueGraph n) = balancedEdgeTarget n ∧
    (∀ S : Finset (Fin n), S.card = 5 → containsTriangle (balancedCliqueGraph n) S)

end

end MathlibPlus.Open.ResearchBatch.GraphBounds
