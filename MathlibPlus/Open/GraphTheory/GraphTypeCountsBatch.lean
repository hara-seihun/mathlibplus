import Mathlib

namespace MathlibPlus.Open.GraphFourier.TypeCountsBatch

/-- Fixed-label graph isomorphism used to quotient graph types. -/
def GraphIsoRelation {n : ℕ}
    (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    ∀ v w : Fin n, G.Adj v w ↔ H.Adj (σ v) (σ w)

noncomputable def graphTypeSetoid (n : ℕ) :
    Setoid (SimpleGraph (Fin n)) where
  r := GraphIsoRelation
  iseqv := by
    constructor
    · intro G
      refine ⟨Equiv.refl _, ?_⟩
      simp
    · intro G H h
      rcases h with ⟨σ, hσ⟩
      refine ⟨σ.symm, ?_⟩
      intro v w
      simpa using (hσ (σ.symm v) (σ.symm w)).symm
    · intro G H K hGH hHK
      rcases hGH with ⟨σ, hσ⟩
      rcases hHK with ⟨τ, hτ⟩
      refine ⟨σ.trans τ, ?_⟩
      intro v w
      exact (hσ v w).trans (hτ (σ v) (σ w))

/-- Spanning means that every vertex is incident with an edge. -/
def HasNoIsolatedVertices {n : ℕ}
    (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, G.Adj v w

def IsConnectedSpanning {n : ℕ}
    (G : SimpleGraph (Fin n)) : Prop :=
  HasNoIsolatedVertices G ∧ G.Connected

def IsDisconnectedSpanning {n : ℕ}
    (G : SimpleGraph (Fin n)) : Prop :=
  HasNoIsolatedVertices G ∧ ¬G.Connected

/-- Count isomorphism classes satisfying a graph-type predicate. -/
noncomputable def graphTypeCount (n : ℕ)
    (p : SimpleGraph (Fin n) → Prop) [DecidablePred p] : ℕ := by
  classical
  letI := graphTypeSetoid n
  exact ((Finset.univ.filter p).image (fun G => Quotient.mk' G)).card

noncomputable def spanningTypeCount (n : ℕ) : ℕ := by
  classical
  exact graphTypeCount n HasNoIsolatedVertices

noncomputable def disconnectedSpanningTypeCount (n : ℕ) : ℕ := by
  classical
  exact graphTypeCount n IsDisconnectedSpanning

noncomputable def connectedSpanningTypeCount (n : ℕ) : ℕ := by
  classical
  exact graphTypeCount n IsConnectedSpanning

/-- Claim 31490: the exact spanning, disconnected-spanning, and
connected-spanning graph-type counts through order seven. -/
def claim31490 : Prop :=
  (spanningTypeCount 2 = 1 ∧ disconnectedSpanningTypeCount 2 = 0 ∧
      connectedSpanningTypeCount 2 = 1) ∧
  (spanningTypeCount 3 = 2 ∧ disconnectedSpanningTypeCount 3 = 0 ∧
      connectedSpanningTypeCount 3 = 2) ∧
  (spanningTypeCount 4 = 7 ∧ disconnectedSpanningTypeCount 4 = 1 ∧
      connectedSpanningTypeCount 4 = 6) ∧
  (spanningTypeCount 5 = 23 ∧ disconnectedSpanningTypeCount 5 = 2 ∧
      connectedSpanningTypeCount 5 = 21) ∧
  (spanningTypeCount 6 = 122 ∧ disconnectedSpanningTypeCount 6 = 10 ∧
      connectedSpanningTypeCount 6 = 112) ∧
  (spanningTypeCount 7 = 888 ∧ disconnectedSpanningTypeCount 7 = 35 ∧
      connectedSpanningTypeCount 7 = 853)

end MathlibPlus.Open.GraphFourier.TypeCountsBatch
