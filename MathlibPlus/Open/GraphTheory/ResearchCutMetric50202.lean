import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.GraphTheory.ResearchCutMetric50202

noncomputable section
open Classical

/-- The finite edge carrier of a finite simple graph. -/
def graphEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeSet.toFinite.toFinset

/-- Edges whose endpoints have the same color in the fixed cut. -/
def monochromaticEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  (graphEdges G).filter (fun e => (e.toFinset.image c).card = 1)

/-- Edges crossing the fixed cut. -/
def crossingEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  (graphEdges G).filter (fun e => (e.toFinset.image c).card = 2)

/-- The crossing graph of the fixed bipartition. -/
def crossingGraph {V : Type*} (G : SimpleGraph V) (c : V → Bool) :
    SimpleGraph V :=
  SimpleGraph.fromRel (fun u v => G.Adj u v ∧ c u ≠ c v)

/-- A maximum cut, expressed by the switching definition. -/
def maximumCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool) : Prop :=
  ∀ S : Finset V,
    (crossingEdges G (fun v => if v ∈ S then !c v else c v)).card ≤
      (crossingEdges G c).card

/-- Triangle-freeness of the underlying simple graph. -/
def triangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃u v w : V⦄,
    u ≠ v → v ≠ w → w ≠ u →
    G.Adj u v → G.Adj v w → G.Adj w u → False

/-- Nontrivial vertex cuts, as used by the fractional metric. -/
def nontrivialCut {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ (Finset.univ : Finset V)

noncomputable def cutFamily {V : Type*} [Fintype V] [DecidableEq V] :
    Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter nontrivialCut

/-- A vertex pair crosses a cut exactly when its two-element endpoint set has
one vertex in the cut. -/
def crossesCut {V : Type*} [DecidableEq V]
    (e : Sym2 V) (S : Finset V) : Prop :=
  (e.toFinset ∩ S).card = 1

/-- The cut boundary of an edge set. -/
def cutBoundaryCount {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (S : Finset V) : ℕ :=
  (E.filter (fun e => crossesCut e S)).card

/-- The finite same-side codegree-zero demand set `D(B)`.  Its universe is
all unordered two-element vertex pairs, not only edges of `G`. -/
def demandPairs {V : Type*} [Fintype V] [DecidableEq V]
    (B : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  (Finset.univ : Finset (Sym2 V)).filter (fun e =>
    e.toFinset.card = 2 ∧
      (e.toFinset.image c).card = 1 ∧
      ¬ ∃ x y z : V,
        x ∈ e.toFinset ∧ y ∈ e.toFinset ∧ x ≠ y ∧
          B.Adj x z ∧ B.Adj y z)

/-- The fractional cut metric `d_lambda`. -/
def cutMetric {V : Type*} [Fintype V] [DecidableEq V]
    (lambda : Finset V → ℝ) (e : Sym2 V) : ℝ :=
  ∑ S ∈ cutFamily (V := V),
    if crossesCut e S then lambda S else 0

/-- The bipartization number `beta(G)`, as the minimum monochromatic-edge
count over all Boolean vertex cuts. -/
noncomputable def bipartizationNumber {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  sInf {n : ℕ | ∃ c : V → Bool, (monochromaticEdges G c).card = n}

/-- Claim 50202: every feasible nonnegative fractional cut metric gives the
full displayed primal certificate for a triangle-free graph with a connected
maximum-cut crossing presentation. -/
def claim50202 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : V → Bool),
    triangleFree G →
    maximumCut G c →
    (crossingGraph G c).Connected →
    ∀ lambda : Finset V → ℝ,
      (∀ S ∈ cutFamily (V := V), 0 ≤ lambda S) →
      (∀ e ∈ demandPairs (crossingGraph G c) c,
        (1 : ℝ) ≤ cutMetric lambda e) →
      let B := crossingGraph G c
      let M := monochromaticEdges G c
      (bipartizationNumber G = M.card) ∧
        (M.card : ℝ) ≤ ∑ e ∈ M, cutMetric lambda e ∧
        (∑ e ∈ M, cutMetric lambda e) =
          ∑ S ∈ cutFamily (V := V),
            lambda S * (cutBoundaryCount M S : ℝ) ∧
        (∑ S ∈ cutFamily (V := V),
            lambda S * (cutBoundaryCount M S : ℝ)) ≤
          ∑ S ∈ cutFamily (V := V),
            lambda S * (cutBoundaryCount B.edgeFinset S : ℝ)

end

end MathlibPlus.Open.GraphTheory.ResearchCutMetric50202
