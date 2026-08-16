import Mathlib
import MathlibPlus.Combinatorics.Claim44521

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus

abbrev GraphType (n : ℕ) :=
  MathlibPlus.Combinatorics.Claim44521.finiteSimpleGraphType n

noncomputable def graphRepresentative {n : ℕ} (Y : GraphType n) : SimpleGraph (Fin n) :=
  Quotient.out Y

noncomputable def graphEdges {n : ℕ} (Y : GraphType n) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.filter (fun e => e ∈ (graphRepresentative Y).edgeSet)

def graphEdgeCount {n : ℕ} (Y : GraphType n) : ℕ :=
  (graphEdges Y).card

def hasNoIsolatedVertices {n : ℕ} (Y : GraphType n) : Prop :=
  ∀ v : Fin n, ∃ w : Fin n, (graphRepresentative Y).Adj v w

abbrev LevelGraphType (n m : ℕ) :=
  {Y : GraphType n // graphEdgeCount Y = m ∧ hasNoIsolatedVertices Y}

noncomputable def edgeVertices {n : ℕ}
    (B : Finset (Sym2 (Fin n))) : Finset (Fin n) := by
  classical
  exact B.biUnion (fun e => e.toFinset)

def blockSpansFewerThan {n : ℕ}
    (B : Finset (Sym2 (Fin n))) : Prop :=
  (edgeVertices B).card < n

def isValidEdgePartition {n : ℕ} (Y : GraphType n)
    (π : Finset (Finset (Sym2 (Fin n)))) : Prop :=
  (∀ B ∈ π, B.Nonempty) ∧
    (∀ B ∈ π, B ⊆ graphEdges Y) ∧
    (∀ e, e ∈ graphEdges Y ↔ ∃ B ∈ π, e ∈ B) ∧
    (∀ B ∈ π, blockSpansFewerThan B) ∧
    (∀ B C, B ∈ π → C ∈ π → B ≠ C →
      ∀ e, e ∈ B → e ∉ C)

noncomputable def validEdgePartitions {n : ℕ} (Y : GraphType n) :
    Finset (Finset (Finset (Sym2 (Fin n)))) := by
  classical
  exact Finset.univ.filter (isValidEdgePartition Y)

noncomputable def blockType {n : ℕ}
    (B : Finset (Sym2 (Fin n))) : GraphType n :=
  MathlibPlus.Combinatorics.Claim44521.graphTypeOf n
    (SimpleGraph.fromEdgeSet (B : Set (Sym2 (Fin n))))

noncomputable def partitionPolynomial {n m : ℕ}
    (Y : LevelGraphType n m) :
    MvPolynomial (GraphType n) ℚ :=
  Finset.sum (validEdgePartitions Y.1) (fun π =>
    Finset.prod π (fun B => MvPolynomial.X (blockType B)))

noncomputable def partitionMonomialSet (n m : ℕ) :
    Finset (GraphType n →₀ ℕ) := by
  classical
  exact (Finset.univ : Finset (LevelGraphType n m)).biUnion
    (fun Y => (partitionPolynomial Y).support)

noncomputable def partitionMatrix (n m : ℕ) :
    Matrix (partitionMonomialSet n m) (LevelGraphType n m) ℚ :=
  fun μ Y => ((partitionPolynomial Y).coeff μ.1 : ℚ)

noncomputable def levelTypeCount (n m : ℕ) : ℕ := by
  classical
  exact Fintype.card (LevelGraphType n m)

noncomputable def privateSignature
    {n m : ℕ} (Y : LevelGraphType n m) : Prop := by
  classical
  exact ∃ μ : GraphType n →₀ ℕ,
    μ ∈ (partitionPolynomial Y).support ∧
      ∀ Z : LevelGraphType n m, Z ≠ Y →
        μ ∉ (partitionPolynomial Z).support

noncomputable def privateSignatureTypeCount (n m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun Y : LevelGraphType n m =>
    privateSignature Y)).card

noncomputable def noPrivateSignatureTypeCount (n m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun Y : LevelGraphType n m =>
    ¬ privateSignature Y)).card

noncomputable def partitionRank (n m : ℕ) : ℕ := by
  classical
  exact Matrix.rank (partitionMatrix n m)

/-- Claim 14347: the exact private-signature failure census, with the actual
finite no-isolated graph-type carrier, valid edge partitions, their
block-type generating polynomials, and the corresponding full matrix ranks. -/
def claim14347_privateSignatureFailureCensus : Prop :=
  let type5 : Fin 8 → ℕ := ![1, 4, 5, 5, 4, 2, 1, 1]
  let noPrivate5 : Fin 8 → ℕ := ![0, 2, 3, 3, 0, 0, 0, 0]
  let type6 : Fin 10 → ℕ := ![1, 3, 9, 15, 20, 22, 20, 14, 9, 5]
  let noPrivate6 : Fin 10 → ℕ := ![0, 0, 6, 12, 16, 18, 14, 7, 2, 0]
  (∀ i : Fin 8,
    levelTypeCount 5 (i.val + 3) = type5 i ∧
      noPrivateSignatureTypeCount 5 (i.val + 3) = noPrivate5 i ∧
        partitionRank 5 (i.val + 3) = type5 i) ∧
    (∀ i : Fin 10,
      levelTypeCount 6 (i.val + 3) = type6 i ∧
        noPrivateSignatureTypeCount 6 (i.val + 3) = noPrivate6 i ∧
          partitionRank 6 (i.val + 3) = type6 i) ∧
    levelTypeCount 6 8 = 22 ∧
      privateSignatureTypeCount 6 8 = 4 ∧
        noPrivateSignatureTypeCount 6 8 = 18 ∧
          partitionRank 6 8 = 22

end MathlibPlus.Open.GraphTheory.PrivateSignatureFailureCensus
