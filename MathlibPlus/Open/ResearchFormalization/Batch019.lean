import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch019

noncomputable section
open scoped BigOperators

/-- The cardinality of the edge set of a finite simple graph. -/
noncomputable def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : Nat := by
  classical
  letI : Fintype G.edgeSet := Set.Finite.fintype (Set.toFinite G.edgeSet)
  exact Fintype.card G.edgeSet

/-- The cardinality of a vertex's finite neighbor set. -/
noncomputable def vertexDegree {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) : Nat := by
  classical
  letI : Fintype (G.neighborSet v) :=
    Set.Finite.fintype (Set.toFinite (G.neighborSet v))
  exact Fintype.card (G.neighborSet v)

/-- The finite type of surviving vertices in a deleted card. -/
noncomputable instance deletedVertexFintype {V : Type} [Fintype V] (z : V) :
    Fintype {v // v ≠ z} :=
  Fintype.ofFinite _

/-- The card obtained by deleting a vertex, with its surviving labels retained as a subtype. -/
def deleteVertex {V : Type} (G : SimpleGraph V) (z : V) : SimpleGraph {v // v ≠ z} :=
  G.induce {v | v ≠ z}

/-- Isomorphism of finite simple graphs, allowing their vertex types to differ. -/
def GraphIsomorphism {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ e : V ≃ W, ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)

/-- Equality of vertex-decks, expressed by a bijection matching every deleted card. -/
def DeckEquivalent {V : Type} (G H : SimpleGraph V) : Prop :=
  ∃ σ : V ≃ V, ∀ z, GraphIsomorphism (deleteVertex G z) (deleteVertex H (σ z))

/-- Unlabelled vertex-deck reconstructibility. -/
def VertexDeckReconstructible {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ H : SimpleGraph V, DeckEquivalent G H → GraphIsomorphism G H

/-- Reconstruction from each specified card, rather than only from the full deck. -/
def ReconstructibleFromAnyCard {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ z (H : SimpleGraph V) (w : V),
    GraphIsomorphism (deleteVertex G z) (deleteVertex H w) →
      GraphIsomorphism G H

/-- The two-connected convention used here: order at least three, connected, and
    vertex deletion leaves a connected graph. -/
def TwoConnected {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧ ∀ z, (deleteVertex G z).Connected

/-- Average degree, recorded as an exact rational rather than a rounded integer. -/
def averageDegree {V : Type} [Fintype V] (G : SimpleGraph V) : ℚ :=
  (2 : ℚ) * edgeCount G / Fintype.card V

/-- The set of degree values occurring in a finite graph. -/
def degreeValues {V : Type} [Fintype V] (G : SimpleGraph V) : Set Nat :=
  {d | ∃ v, vertexDegree G v = d}

/-- No two values in the degree set are consecutive. -/
def NoConsecutiveDegreeValues {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ d, d ∈ degreeValues G → d + 1 ∉ degreeValues G

/-- The local degree and adjacency information supplied by a card. -/
def CardDegreeReconstruction {V : Type} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ (z : V) (u : {v // v ≠ z}),
    (vertexDegree G u.1 = vertexDegree (deleteVertex G z) u ∨
      vertexDegree G u.1 = vertexDegree (deleteVertex G z) u + 1) ∧
    ((vertexDegree (deleteVertex G z) u ∈ degreeValues G ∧
        vertexDegree (deleteVertex G z) u + 1 ∉ degreeValues G) ∨
      (vertexDegree (deleteVertex G z) u ∉ degreeValues G ∧
        vertexDegree (deleteVertex G z) u + 1 ∈ degreeValues G)) ∧
    (G.Adj u.1 z ↔ vertexDegree (deleteVertex G z) u + 1 ∈ degreeValues G)

/-- Iteration of a permutation, used to make the exponent in Claim 27173
    explicit without relying on a notation choice. -/
def iteratePerm {α : Type} (h : Equiv.Perm α) : Nat → α → α
  | 0, x => x
  | r + 1, x => h (iteratePerm h r x)

/-- Claim 27166: a degree set with no consecutive values reconstructs a graph
    from any one vertex card, with the stated degree/adjacency test. -/
def noConsecutiveDegreeValuesOneCardReconstruction : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    3 ≤ Fintype.card V →
      NoConsecutiveDegreeValues G →
      (ReconstructibleFromAnyCard G ∧ CardDegreeReconstruction G)

/-- A minimum-degree threshold is realizable by an exactly-r-edge simple graph. -/
def RealizableMinimumDegree (r k : Nat) : Prop :=
  ∃ v : Nat, 0 < v ∧ ∃ G : SimpleGraph (Fin v),
    edgeCount G = r ∧ ∀ x, k ≤ vertexDegree G x

/-- The ceiling of x/2 in natural-number arithmetic. -/
def ceilHalf (x : Nat) : Nat :=
  (x + 1) / 2

/-- The numerical threshold appearing in the exact minimum-degree formula. -/
def DegreeThreshold (r k : Nat) : Prop :=
  ∃ v : Nat,
    k + 1 ≤ v ∧ ceilHalf (k * v) ≤ r ∧ r ≤ Nat.choose v 2

/-- The finite maximum over all possible minimum-degree thresholds. -/
noncomputable def maximumPossibleMinimumDegree (r : Nat) : Nat := by
  classical
  exact (Finset.range (r + 1)).sup (fun k => if RealizableMinimumDegree r k then k else 0)

/-- Claim 27138: the maximum possible minimum degree at edge rank r is exactly
    the stated ceiling/binomial threshold, including the three numerical checks. -/
def exactMaximumPossibleMinimumDegree : Prop :=
  (∀ r k, RealizableMinimumDegree r k ↔ k ≤ maximumPossibleMinimumDegree r) ∧
  (∀ r k, k ≤ maximumPossibleMinimumDegree r ↔ DegreeThreshold r k) ∧
  maximumPossibleMinimumDegree 6 = 3 ∧
  maximumPossibleMinimumDegree 7 = 2 ∧
  maximumPossibleMinimumDegree 8 = 3

/-- Claim 27165: low-excess two-connected graphs reconstruct, and every
    counterexample has all of the recorded excess and average-degree bounds. -/
def exactLowExcessTwoConnectedClosure : Prop :=
  (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      TwoConnected G → edgeCount G - Fintype.card V ≤ 3 →
        VertexDeckReconstructible G) ∧
  (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      TwoConnected G → ¬ VertexDeckReconstructible G →
        4 ≤ edgeCount G - Fintype.card V ∧
        5 ≤ edgeCount G - Fintype.card V + 1 ∧
        3 * Fintype.card V ≤ 16 * (edgeCount G - Fintype.card V) ∧
        (19 : ℚ) / 8 ≤ averageDegree G ∧
        (7 : ℚ) / 3 < averageDegree G)

/-- Claim 27173: a permutation carrying the parent set to the target set
    cannot postpone the required three-slot state transport. -/
def threeSlotTransportNoDelayedOrientationRepair : Prop :=
  ∀ {α : Type} [DecidableEq α] (u a b : α),
    u ≠ a → u ≠ b → a ≠ b →
    ∀ (h : Equiv.Perm α) (r : Nat),
      Finset.image h {a, b} = {u, b} →
      0 < r →
      (iteratePerm h r u = a ∧
        Finset.image (iteratePerm h r) {a, b} = {u, b}) →
      h u = a ∧ Finset.image h {a, b} = {u, b}

end
end MathlibPlus.Open.ResearchFormalization.Batch019
