import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.R3314

noncomputable section

structure FiniteGraph (n : ℕ) where
  edges : Finset (Fin n × Fin n)


def simpleGraph {n : ℕ} (G : FiniteGraph n) : Prop :=
  ∀ e ∈ G.edges, e.1 < e.2

def edgePresent {n : ℕ} (G : FiniteGraph n) (u v : Fin n) : Prop :=
  (u, v) ∈ G.edges ∨ (v, u) ∈ G.edges

def internalEdges {n : ℕ} (G : FiniteGraph n) (A : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  G.edges.filter (fun e => e.1 ∈ A ∧ e.2 ∈ A)

def crossingEdges {n : ℕ} (G : FiniteGraph n) (A : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  G.edges.filter (fun e => (e.1 ∈ A) ≠ (e.2 ∈ A))

def monochromaticEdges {n : ℕ} (G : FiniteGraph n) (A : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  G.edges.filter (fun e => (e.1 ∈ A) = (e.2 ∈ A))

def cutBoundary {n : ℕ} (G : FiniteGraph n) (X : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  G.edges.filter (fun e => (e.1 ∈ X) ≠ (e.2 ∈ X))

def bipartization {n : ℕ} (G : FiniteGraph n) : ℕ :=
  sInf {b : ℕ | ∃ A : Finset (Fin n),
    b = (internalEdges G A).card +
      (internalEdges G (Finset.univ \ A)).card}

def triangleFree {n : ℕ} (G : FiniteGraph n) : Prop :=
  ∀ i j k : Fin n, i ≠ j → j ≠ k → i ≠ k →
    ¬ (edgePresent G i j ∧ edgePresent G j k ∧ edgePresent G i k)

def maximumCut {n : ℕ} (G : FiniteGraph n) (A : Finset (Fin n)) : Prop :=
  ∀ C : Finset (Fin n), (crossingEdges G C).card ≤ (crossingEdges G A).card

def c5 : FiniteGraph 5 :=
  ⟨{(0, 1), (1, 2), (2, 3), (3, 4), (0, 4)}⟩

def clone0to2 : FiniteGraph 5 :=
  ⟨{(0, 1), (1, 2), (2, 3), (3, 4), (0, 3)}⟩

def clone2to0 : FiniteGraph 5 :=
  ⟨{(0, 1), (1, 2), (2, 4), (0, 4), (3, 4)}⟩

def claim47205 : Prop :=
  simpleGraph c5 ∧ simpleGraph clone0to2 ∧ simpleGraph clone2to0 ∧
  bipartization c5 = 1 ∧
  bipartization clone0to2 = 0 ∧
  bipartization clone2to0 = 0 ∧
  triangleFree c5 ∧ triangleFree clone0to2 ∧ triangleFree clone2to0 ∧
  max (bipartization clone0to2) (bipartization clone2to0) = 0 ∧
  0 < bipartization c5

def claim47207 : Prop :=
  claim47205 ∧
  ¬ (max (bipartization clone0to2) (bipartization clone2to0) ≥
      bipartization c5)

def claim47208 : Prop :=
  ∀ (n : ℕ) (G : FiniteGraph n) (A : Finset (Fin n)), simpleGraph G →
    maximumCut G A →
    ∀ X : Finset (Fin n),
      ((monochromaticEdges G A) ∩ cutBoundary G X).card ≤
        ((crossingEdges G A) ∩ cutBoundary G X).card

end

end MathlibPlus.Open.Research.R3314
