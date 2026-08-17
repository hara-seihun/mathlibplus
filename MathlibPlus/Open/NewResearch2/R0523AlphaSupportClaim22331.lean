import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0523AlphaSupport

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

private def independentVertexSet {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ S → v ∈ S → u ≠ v → ¬ F.Adj u v

private def alphaR {V : Type*} [DecidableEq V]
    (F : SimpleGraph V) (R J : Finset V) : ℕ :=
  (J.filter (fun v =>
    independentVertexSet F (J.erase v) ∧
      (J.erase v ∩ R).card = 0)).card

private def inducedEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (J : Finset V) : ℕ :=
  (Finset.univ.filter (fun e : Sym2 {w // w ∈ J} =>
    e ∈ (F.induce (J : Set V)).edgeSet)).card

private def inducedStarWithIsolatedVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (J : Finset V) : Prop :=
  ∃ c : {v // v ∈ J},
    2 ≤ inducedEdgeCount F J ∧
      ∀ u v : {w // w ∈ J},
        (F.induce (J : Set V)).Adj u v → u = c ∨ v = c

private def inducedVertexCoverAtMostOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (J : Finset V) : Prop :=
  inducedEdgeCount F J = 0 ∨
    ∃ c : {v // v ∈ J},
      ∀ u v : {w // w ∈ J},
        (F.induce (J : Set V)).Adj u v → u = c ∨ v = c

/-- Claim 22331: the coefficient `alpha_R` is classified by the induced
forest on `J`, with the separate one-root case and the vanishing multi-root
case.  The final equivalence records the complete support seen by the
singleton-component derivative. -/
def alphaSupportClassification_claim22331 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (R J : Finset V),
    F.IsAcyclic →
      ((J ∩ R).card = 0 →
        (inducedEdgeCount F J = 0 → alphaR F R J = J.card) ∧
        (inducedEdgeCount F J = 1 → alphaR F R J = 2) ∧
        (inducedStarWithIsolatedVertices F J → alphaR F R J = 1) ∧
        (inducedEdgeCount F J ≠ 0 →
          inducedEdgeCount F J ≠ 1 →
          ¬ inducedStarWithIsolatedVertices F J →
          alphaR F R J = 0)) ∧
      ((J ∩ R).card = 1 →
        ∀ ρ, ρ ∈ J ∩ R →
          (alphaR F R J = 1 ↔
            independentVertexSet F (J.erase ρ))) ∧
      (2 ≤ (J ∩ R).card → alphaR F R J = 0) ∧
      (J.Nonempty ∧ alphaR F R J ≠ 0 ↔
        (((J ∩ R).card = 0 ∧ inducedVertexCoverAtMostOne F J) ∨
          ((J ∩ R).card = 1 ∧
            ∃ ρ, ρ ∈ J ∩ R ∧
              independentVertexSet F (J.erase ρ))))

end

end MathlibPlus.Open.NewResearch2.R0523AlphaSupport
