import Mathlib
import MathlibPlus.GraphTheory.Claim24821_24823

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0799Claim24825

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev FiniteTree (m : ℕ) := {G : SimpleGraph (Fin m) // G.IsTree}
private abbrev Edge (m : ℕ) := Fin m × Fin m

private def treeDegree {m : ℕ} (T : FiniteTree m) (v : Fin m) : ℕ :=
  letI : DecidableRel T.1.Adj := Classical.decRel _
  MathlibPlus.GraphTheory.Claim24821.rootDegree_claim24821 T.1 v

private def treeNeighborLoad {m : ℕ} (T : FiniteTree m) (v : Fin m) : ℕ :=
  letI : DecidableRel T.1.Adj := Classical.decRel _
  MathlibPlus.GraphTheory.Claim24823.additiveNeighborLoad_claim24823 T.1 v

private def treeEdges {m : ℕ} (T : FiniteTree m) : Finset (Edge m) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ T.1.Adj e.1 e.2)

private def edgeIncident {m : ℕ} (e : Edge m) (v : Fin m) : Prop :=
  e.1 = v ∨ e.2 = v

private def edgeDisjoint {m : ℕ} (e f : Edge m) : Prop :=
  ¬ ∃ w : Fin m, edgeIncident e w ∧ edgeIncident f w

private def disjointPairWithOneRootEdge {m : ℕ}
    (S : Finset (Edge m)) (v : Fin m) : Prop :=
  S.card = 2 ∧
    ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧ edgeDisjoint e f ∧
      edgeIncident e v ∧ ¬ edgeIncident f v

private def disjointPairCount {m : ℕ} (T : FiniteTree m)
    (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    disjointPairWithOneRootEdge S v)).card

private def rootNeighborSum {m : ℕ} (T : FiniteTree m) (v : Fin m) : ℤ :=
  ∑ u : Fin m,
    if T.1.Adj v u then
      (m : ℤ) - (treeDegree T v : ℤ) - (treeDegree T u : ℤ)
    else 0

/-- Claim 24825: the selected-edge count B_v equals both the displayed
neighbor sum and the degree/load expression, with the exact finite-tree and
root carriers retained. -/
def disjointSelectedPairCount_claim24825 : Prop :=
  ∀ (m : ℕ) (T : FiniteTree m) (v : Fin m),
    (disjointPairCount T v : ℤ) = rootNeighborSum T v ∧
      rootNeighborSum T v =
        (treeDegree T v : ℤ) *
            ((m : ℤ) - (treeDegree T v : ℤ) - 1) -
          (treeNeighborLoad T v : ℤ)

end

end MathlibPlus.Open.ResearchFormalization.R0799Claim24825
