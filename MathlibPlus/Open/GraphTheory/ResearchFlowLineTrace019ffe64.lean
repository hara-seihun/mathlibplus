import Mathlib

namespace MathlibPlus.Open.GraphTheory.ResearchFormalizationBatch019ffe64

open scoped BigOperators

noncomputable section

/-- The oriented incidence of a real edge-weighting, with columns
    `e_tail - e_head`. -/
def realIncidence {V E : Type*} [Fintype E]
    (tail head : E → V) (f : E → ℝ) (v : V) : ℝ := by
  classical
  exact (∑ e : E, ((if tail e = v then f e else 0) -
    (if head e = v then f e else 0)))

def integerIncidence {V E : Type*} [Fintype E]
    (tail head : E → V) (f : E → ℕ) (v : V) : ℤ := by
  classical
  exact (∑ e : E, ((if tail e = v then (f e : ℤ) else 0) -
    (if head e = v then (f e : ℤ) else 0)))

def realUnitDemand {V : Type*} (α ω : V) (v : V) : ℝ := by
  classical
  exact if v = α then 1 else if v = ω then -1 else 0

def integerUnitDemand {V : Type*} (α ω : V) (v : V) : ℤ := by
  classical
  exact if v = α then 1 else if v = ω then -1 else 0

def directedReachable {V E : Type*}
    (tail head : E → V) (α ω : V) : Prop :=
  Relation.ReflTransGen (fun p q => ∃ e : E, tail e = p ∧ head e = q) α ω

def forwardClosed {V E : Type*}
    (tail head : E → V) (S : Set V) : Prop :=
  ∀ e : E, tail e ∈ S → head e ∈ S

def separatingPotential {V E : Type*}
    (tail head : E → V) (α ω : V) : Prop :=
  ∃ φ : V → ℝ,
    (∀ e : E, 0 ≤ φ (tail e) - φ (head e)) ∧
      φ α - φ ω < 0

/-- Real nonnegative flow, integral flow, reachability, forward cuts, and
    separating potentials are the five equivalent formulations of an
    alpha-to-omega unit flow. -/
def rationalFlowPathCutClaim50519 : Prop :=
  ∀ {V E : Type*} [Fintype V] [Fintype E]
    (tail head : E → V) (α ω : V), α ≠ ω →
      ((∃ f : E → ℝ,
          (∀ e : E, 0 ≤ f e) ∧
            ∀ v : V, realIncidence tail head f v =
              realUnitDemand α ω v) ↔
        (∃ f : E → ℕ,
          ∀ v : V, integerIncidence tail head f v =
            integerUnitDemand α ω v)) ∧
      ((∃ f : E → ℝ,
          (∀ e : E, 0 ≤ f e) ∧
            ∀ v : V, realIncidence tail head f v =
              realUnitDemand α ω v) ↔
        directedReachable tail head α ω) ∧
      ((directedReachable tail head α ω) ↔
        ¬ ∃ S : Set V,
          α ∈ S ∧ ω ∉ S ∧ forwardClosed tail head S) ∧
      ((directedReachable tail head α ω) ↔
        ¬ separatingPotential tail head α ω)

/-- The line graph of a vertex-deleted card is the induced line graph obtained
    by removing the host vertex's incidence star. -/
def lineGraphStarDeletionTraceClaim50539 : Prop :=
  ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (v : V),
    Nonempty ((G.induce {x : V | x ≠ v}).lineGraph ≃g
      G.lineGraph.induce
        {e : G.edgeSet | (e : Sym2 V) ∉ G.incidenceSet v})

end

end MathlibPlus.Open.GraphTheory.ResearchFormalizationBatch019ffe64
