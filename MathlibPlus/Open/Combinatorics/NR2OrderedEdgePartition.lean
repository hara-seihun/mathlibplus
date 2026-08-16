import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.NR2

noncomputable section

/-- A finite graph is represented on a standard finite vertex carrier. -/
abbrev FiniteGraph := Sigma (fun k : ℕ => SimpleGraph (Fin k))

/-- The isomorphism class of a labeled graph on `Fin n`. -/
def graphTypeClass {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Set (SimpleGraph (Fin n)) :=
  {Z | Nonempty (Y ≃g Z)}

/-- The unordered finite edge set of a labeled simple graph. -/
def graphEdgeFinset {n : ℕ} (Y : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ Y.edgeSet)

/-- The graph carried by an edge block, with its incident vertices and no
artificial isolated vertices retained. -/
def blockFiniteGraph {n : ℕ} (B : Finset (Sym2 (Fin n))) : FiniteGraph :=
  let G : SimpleGraph (Fin n) :=
    SimpleGraph.fromEdgeSet (B : Set (Sym2 (Fin n)))
  let H : SimpleGraph G.support := G.induce G.support
  ⟨Fintype.card G.support,
    H.comap (Fintype.equivFin G.support).symm⟩

/-- A block variable is indexed by the isomorphism type of its incident
finite graph. -/
def blockGraphType {n : ℕ} (B : Finset (Sym2 (Fin n))) :
    Set FiniteGraph :=
  {K | Nonempty ((blockFiniteGraph B).2 ≃g K.2)}

/-- The vertices incident with an edge block number fewer than `n`. -/
def blockSpansFewerThan {n : ℕ} (B : Finset (Sym2 (Fin n))) : Prop :=
  Fintype.card
      ((SimpleGraph.fromEdgeSet (B : Set (Sym2 (Fin n)))).support) < n

/-- A genuine set partition of the edge set whose nonempty blocks span fewer
than all `n` vertices. -/
def admissibleEdgePartition {n : ℕ} (Y : SimpleGraph (Fin n))
    (π : Finset (Finset (Sym2 (Fin n)))) : Prop :=
  (∀ B ∈ π,
    B.Nonempty ∧ B ⊆ graphEdgeFinset Y ∧ blockSpansFewerThan B) ∧
    π.biUnion id = graphEdgeFinset Y ∧
    (∀ B ∈ π, ∀ C ∈ π, B ≠ C → Disjoint B C)

/-- The ordered-edge-partition polynomial of a representative of a graph
type. -/
noncomputable def orderedEdgePartitionPolynomial {n : ℕ}
    (Y : SimpleGraph (Fin n)) : MvPolynomial (Set FiniteGraph) ℤ := by
  classical
  exact ∑ π ∈
      (Finset.univ.filter
        (fun π : Finset (Finset (Sym2 (Fin n))) =>
          admissibleEdgePartition Y π)),
    ∏ B ∈ π, MvPolynomial.X (blockGraphType B)

/-- The no-isolated-vertex condition on an `n`-vertex graph. -/
def hasNoIsolatedVertices {n : ℕ} (Y : SimpleGraph (Fin n)) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, Y.Adj v w

/-- The graph-type support selected at a fixed edge level. -/
noncomputable def edgeLevelGraphTypes (n m : ℕ) :
    Finset (Set (SimpleGraph (Fin n))) := by
  classical
  exact (Finset.univ.image
      (fun Y : SimpleGraph (Fin n) => graphTypeClass Y)).filter
    (fun C =>
      ∃ Y : SimpleGraph (Fin n),
        C = graphTypeClass Y ∧
          hasNoIsolatedVertices Y ∧ (graphEdgeFinset Y).card = m)

/-- Claim 15600: the polynomial is the exact sum over admissible edge
partitions, its variables retain full block isomorphism types, and the level
support contains exactly the no-isolated graph types with the prescribed edge
count. -/
def orderedEdgePartitionPolynomial_claim15600 : Prop := by
  classical
  exact ∀ (n m : ℕ) (Y : SimpleGraph (Fin n)),
    hasNoIsolatedVertices Y →
    (orderedEdgePartitionPolynomial Y =
      ∑ π ∈
        (Finset.univ.filter
          (fun π : Finset (Finset (Sym2 (Fin n))) =>
            admissibleEdgePartition Y π)),
        ∏ B ∈ π, MvPolynomial.X (blockGraphType B)) ∧
    (∀ Z : SimpleGraph (Fin n),
      Nonempty (Y ≃g Z) →
        orderedEdgePartitionPolynomial Z = orderedEdgePartitionPolynomial Y) ∧
    (graphTypeClass Y ∈ edgeLevelGraphTypes n m ↔
      (graphEdgeFinset Y).card = m)

end

end MathlibPlus.Open.Combinatorics.NR2
