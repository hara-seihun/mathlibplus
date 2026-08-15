import Mathlib

namespace MathlibPlus.Open.FormalizationBatchGraphs

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V]

/-- A clique and an independent set inside a finite vertex set. -/
def cliqueOn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → G.Adj u v

def independentOn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → ¬G.Adj u v

def containsClique (G : SimpleGraph V) (s : Finset V) (n : ℕ) : Prop :=
  ∃ t : Finset V, t ⊆ s ∧ t.card = n ∧ cliqueOn G t

def containsIndependent (G : SimpleGraph V) (s : Finset V) (n : ℕ) : Prop :=
  ∃ t : Finset V, t ⊆ s ∧ t.card = n ∧ independentOn G t

def noClique (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ s : Finset V, s.card = n → ¬cliqueOn G s

def noIndependent (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ s : Finset V, s.card = n → ¬independentOn G s

def good55 (G : SimpleGraph V) : Prop :=
  noClique G 5 ∧ noIndependent G 5

def graphDegree (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w => G.Adj v w)).card

def externalVertices (u v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => w ≠ u ∧ w ≠ v)

def commonNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact (externalVertices u v).filter (fun w => G.Adj u w ∧ G.Adj v w)

def commonNonneighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact (externalVertices u v).filter (fun w => ¬G.Adj u w ∧ ¬G.Adj v w)

def oneSidedNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact (externalVertices u v).filter (fun w => G.Adj u w ∧ ¬G.Adj v w)

def theOtherSidedNeighbors (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact (externalVertices u v).filter (fun w => ¬G.Adj u w ∧ G.Adj v w)

def externalAdjacencyDifference (G : SimpleGraph V) (u v : V) : Finset V := by
  classical
  exact (externalVertices u v).filter
    (fun w => (G.Adj u w ∧ ¬G.Adj v w) ∨ (¬G.Adj u w ∧ G.Adj v w))

/-- In every 43-vertex (5,5)-good graph, all degrees are in [18,24]. -/
def degreeIntervalClaim20348 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = 43 →
    good55 G →
    ∀ v : V, 18 ≤ graphDegree G v ∧ graphDegree G v ≤ 24

/-- The two common-set Ramsey bounds, including the forbidden subconfigurations. -/
def commonSetRamseyBoundsClaim20349 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = 43 →
    good55 G →
    ∀ ⦃u v : V⦄, u ≠ v →
      (G.Adj u v →
        ¬containsClique G (commonNeighbors G u v) 3 ∧
        ¬containsIndependent G (commonNeighbors G u v) 5 ∧
        (commonNeighbors G u v).card ≤ 13) ∧
      (¬G.Adj u v →
        ¬containsClique G (commonNonneighbors G u v) 5 ∧
        ¬containsIndependent G (commonNonneighbors G u v) 3 ∧
        (commonNonneighbors G u v).card ≤ 13)

/-- For an adjacent pair, the two one-sided parts have the stated lower bound. -/
def adjacentExternalAdjacencyClaim20350 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = 43 →
    good55 G →
    ∀ ⦃u v : V⦄, u ≠ v → G.Adj u v →
      let a := (commonNeighbors G u v).card
      let δ := (oneSidedNeighbors G u v).card +
        (theOtherSidedNeighbors G u v).card
      8 ≤ 34 - 2 * a ∧ 34 - 2 * a ≤ δ

/-- For a nonadjacent pair, the partition inequalities and their consequences. -/
def nonadjacentExternalAdjacencyClaim20351 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = 43 →
    good55 G →
    ∀ ⦃u v : V⦄, u ≠ v → ¬G.Adj u v →
      let a := (commonNeighbors G u v).card
      let δ := (oneSidedNeighbors G u v).card +
        (theOtherSidedNeighbors G u v).card
      δ ≤ 48 - 2 * a ∧ 28 - a ≤ δ ∧ a ≤ 20 ∧ 8 ≤ δ

/-- The external symmetric-difference distance is at least eight. -/
def universalPairNeighborhoodDistanceClaim20352 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = 43 →
    good55 G →
    ∀ ⦃u v : V⦄, u ≠ v →
      8 ≤ (externalAdjacencyDifference G u v).card

/-- A graph automorphism and its moved-point support. -/
def graphAutomorphism (G : SimpleGraph V) (σ : V → V) : Prop :=
  Function.Bijective σ ∧ ∀ u v : V, G.Adj (σ u) (σ v) ↔ G.Adj u v

def automorphismSupport (σ : V → V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => σ w ≠ w)

/-- Fixed vertices distinguish no moved pair, so the support bounds its distance. -/
def automorphismSupportClaim20353 : Prop :=
  ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) (σ : V → V),
    graphAutomorphism G σ →
    ∀ ⦃u : V⦄, σ u ≠ u →
      (∀ w : V, σ w = w → G.Adj u w ↔ G.Adj (σ u) w) ∧
      (externalAdjacencyDifference G u (σ u)).card ≤
        (automorphismSupport σ).card - 2

end

end MathlibPlus.Open.FormalizationBatchGraphs
