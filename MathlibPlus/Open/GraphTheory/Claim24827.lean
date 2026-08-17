import Mathlib
import MathlibPlus.GraphTheory.Claim24821_24823

open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace MathlibPlus.Open.GraphTheory.Claim24827

private abbrev Poly := MvPolynomial (Option ℕ) ℤ
private def z : Poly := MvPolynomial.X none
private def x (i : ℕ) : Poly := MvPolynomial.X (some i)

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

private def edgeDisjoint {m : ℕ} (e f : Edge m) : Prop :=
  ¬ ∃ v : Fin m, edgeIncident e v ∧ edgeIncident f v

private def selectedAdj {m : ℕ} (S : Finset (Edge m))
    (u v : Fin m) : Prop :=
  (u < v ∧ (u, v) ∈ S) ∨ (v < u ∧ (v, u) ∈ S)

private def selectedReachable {m : ℕ} (S : Finset (Edge m))
    (u v : Fin m) : Prop :=
  Relation.ReflTransGen (selectedAdj S) u v

private def component {m : ℕ} (S : Finset (Edge m))
    (v : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun u => selectedReachable S v u)

private def componentSize {m : ℕ} (S : Finset (Edge m))
    (v : Fin m) : ℕ :=
  (component S v).card

private def componentMinima {m : ℕ} (S : Finset (Edge m)) : Finset (Fin m) :=
  Finset.univ.filter (fun v =>
    ∀ u, selectedReachable S u v → v ≤ u)

private def componentProduct {m : ℕ} (S : Finset (Edge m)) : Poly :=
  (componentMinima S).prod (fun v => x (componentSize S v))

private def componentProductExcept {m : ℕ} (S : Finset (Edge m))
    (r : Fin m) : Poly :=
  ((componentMinima S).filter (fun v =>
    ¬ selectedReachable S r v)).prod (fun v => x (componentSize S v))

private def openState {m : ℕ} (S : Finset (Edge m))
    (r : Fin m) : Poly :=
  if 1 < componentSize S r then
    z ^ componentSize S r * componentProductExcept S r
  else
    0

private def closedForestPolynomial {m : ℕ} (T : FiniteTree m) : Poly :=
  (treeEdges T).powerset.sum (fun S => componentProduct S)

private def rootedForestPolynomial {m : ℕ} (T : FiniteTree m)
    (r : Fin m) : Poly :=
  closedForestPolynomial T +
    (treeEdges T).powerset.sum (fun S => openState S r)

private def rerootDifference {m : ℕ} (T : FiniteTree m)
    (r s : Fin m) : Poly :=
  rootedForestPolynomial T r - rootedForestPolynomial T s

private def exponentDefect (e : Option ℕ →₀ ℕ) : ℕ :=
  e none + e.support.sum (fun q =>
    match q with
    | none => 0
    | some i => e (some i) * (i - 1))

private def defectLayer (p : Poly) (j : ℕ) : Poly :=
  (p.support.filter (fun e => exponentDefect e = j)).sum
    (fun e => MvPolynomial.monomial e (p.coeff e))

private def adjacentTwoEdgePath {m : ℕ} (S : Finset (Edge m)) : Prop :=
  S.card = 2 ∧ ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧
    ∃ w : Fin m, edgeIncident e w ∧ edgeIncident f w

private def adjacentPairCount {m : ℕ} (T : FiniteTree m)
    (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    adjacentTwoEdgePath S ∧ ∃ e ∈ S, edgeIncident e v)).card

private def disjointPairWithOneRootEdge {m : ℕ}
    (S : Finset (Edge m)) (v : Fin m) : Prop :=
  S.card = 2 ∧ ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧ edgeDisjoint e f ∧
    edgeIncident e v ∧ ¬ edgeIncident f v

private def disjointPairCount {m : ℕ} (T : FiniteTree m)
    (v : Fin m) : ℕ :=
  ((treeEdges T).powerset.filter (fun S =>
    disjointPairWithOneRootEdge S v)).card

private def Q3 : Poly :=
  z ^ 3 * x 1 ^ 2 - z ^ 2 * x 1 * x 2 -
    z * x 1 * x 3 + z * x 2 ^ 2

/-- Claim 24827: on an equal-degree reroot axis, retain both selected-edge
count identities and the resulting complete defect-three polynomial. -/
def claim24827 : Prop :=
  ∀ (m : ℕ) (T : FiniteTree m) (r s : Fin m),
    treeDegree T r = treeDegree T s →
      ((adjacentPairCount T r : ℤ) - adjacentPairCount T s =
          (treeNeighborLoad T r : ℤ) - treeNeighborLoad T s) ∧
      ((disjointPairCount T r : ℤ) - disjointPairCount T s =
          -((treeNeighborLoad T r : ℤ) - treeNeighborLoad T s)) ∧
      defectLayer (rerootDifference T r s) 3 =
        MvPolynomial.C
            ((treeNeighborLoad T r : ℤ) - treeNeighborLoad T s) *
          (x 1 ^ (m - 5) * Q3)

end MathlibPlus.Open.GraphTheory.Claim24827
