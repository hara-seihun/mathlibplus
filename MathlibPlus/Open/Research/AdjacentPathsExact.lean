import MathlibPlus.GraphTheory.Claim24821_24823

open scoped BigOperators

namespace MathlibPlus.Open.Research.AdjacentPathsExact

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

private abbrev FiniteTree (m : ℕ) := {G : SimpleGraph (Fin m) // G.IsTree}

private noncomputable def treeDegree {m : ℕ}
    (T : FiniteTree m) (v : Fin m) : ℕ :=
  letI : DecidableRel T.1.Adj := Classical.decRel _
  MathlibPlus.GraphTheory.Claim24821.rootDegree_claim24821 T.1 v

private noncomputable def treeNeighborLoad {m : ℕ}
    (T : FiniteTree m) (v : Fin m) : ℕ :=
  letI : DecidableRel T.1.Adj := Classical.decRel _
  MathlibPlus.GraphTheory.Claim24823.additiveNeighborLoad_claim24823 T.1 v

private abbrev Edge (m : ℕ) := Fin m × Fin m

private def treeEdges {m : ℕ} (T : FiniteTree m) : Finset (Edge m) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ T.1.Adj e.1 e.2)

private def edgeIncident {m : ℕ} (e : Edge m) (v : Fin m) : Prop :=
  e.1 = v ∨ e.2 = v

private def adjacentTwoEdgePath {m : ℕ} (S : Finset (Edge m)) : Prop :=
  S.card = 2 ∧ ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧
    ∃ w : Fin m, edgeIncident e w ∧ edgeIncident f w

private def adjacentPairCount {m : ℕ} (T : FiniteTree m)
    (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    adjacentTwoEdgePath S ∧ ∃ e ∈ S, edgeIncident e v)).card

/-- Every selected adjacent two-edge path through a root is either centered at
that root or has the root as an endpoint, giving A_v = binom(d_v,2)+N_v. -/
def claim24824 : Prop :=
  ∀ m : ℕ, ∀ T : FiniteTree m, ∀ v : Fin m,
    adjacentPairCount T v =
      Nat.choose (treeDegree T v) 2 + treeNeighborLoad T v

end
end MathlibPlus.Open.Research.AdjacentPathsExact
