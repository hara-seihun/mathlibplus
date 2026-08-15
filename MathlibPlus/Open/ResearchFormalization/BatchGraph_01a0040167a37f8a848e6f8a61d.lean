import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Finite triangle-free maximum-cut inequalities. -/

def graphNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => G.Adj v u)

def graphCrosses (A : Set V) (v u : V) : Prop :=
  (v ∈ A ∧ u ∉ A) ∨ (v ∉ A ∧ u ∈ A)

def graphSameSide (A : Set V) (v u : V) : Prop :=
  (v ∈ A ∧ u ∈ A) ∨ (v ∉ A ∧ u ∉ A)

def crossingNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : Finset V := by
  classical
  exact (graphNeighbors G v).filter (fun u => graphCrosses A v u)

def sameSideNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : Finset V := by
  classical
  exact (graphNeighbors G v).filter (fun u => graphSameSide A v u)

def crossingDegreeNat {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : ℕ :=
  (crossingNeighbors G A v).card

def sameSideDegreeNat {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : ℕ :=
  (sameSideNeighbors G A v).card

def cDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : ℤ :=
  crossingDegreeNat G A v

def mDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : ℤ :=
  sameSideDegreeNat G A v

def sDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : ℤ :=
  cDegree G A v - mDegree G A v

def cutScore {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) : ℕ := by
  classical
  exact ∑ v : V, crossingDegreeNat G A v

def triangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v w : V⦄, G.Adj u v → G.Adj v w → G.Adj w u →
    u = v ∨ v = w ∨ u = w

def maximumCut {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) : Prop :=
  ∀ X : Set V, cutScore G X ≤ cutScore G A

def cutHypotheses {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A B : Set V) : Prop :=
  triangleFree G ∧ Disjoint A B ∧ A ∪ B = Set.univ ∧ maximumCut G A

def claim46709 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Set V),
    cutHypotheses G A B →
      ∀ v : V,
        0 ≤ sDegree G A v ∧
          (∑ u ∈ crossingNeighbors G A v, sDegree G A u) ≥
            cDegree G A v + mDegree G A v

def internalANeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : Finset V := by
  classical
  exact (graphNeighbors G v).filter (fun u => v ∈ A ∧ u ∈ A)

def internalBNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) (v : V) : Finset V := by
  classical
  exact (graphNeighbors G v).filter (fun u => v ∉ A ∧ u ∉ A)

def internalAEdgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) : ℕ := by
  classical
  exact (∑ v : V, (internalANeighbors G A v).card) / 2

def internalBEdgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) : ℕ := by
  classical
  exact (∑ v : V, (internalBNeighbors G A v).card) / 2

def crossingEdgeCount {V : Type*} [Fintype V]
    (G : SimpleGraph V) (A : Set V) : ℕ := by
  classical
  exact (∑ v : V, (crossingNeighbors G A v).card) / 2

def setSum {V : Type*} [Fintype V] (B : Set V) (f : V → ℤ) : ℤ := by
  classical
  exact ∑ v ∈ (Finset.univ.filter (fun v => v ∈ B)), f v

def claim46712 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (A B : Set V),
    cutHypotheses G A B →
      setSum B (fun u => cDegree G A u * sDegree G A u) ≥
          (crossingEdgeCount G A : ℤ) + 2 * (internalAEdgeCount G A : ℤ) ∧
        setSum A (fun u => cDegree G A u * sDegree G A u) ≥
          (crossingEdgeCount G A : ℤ) + 2 * (internalBEdgeCount G A : ℤ)


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
