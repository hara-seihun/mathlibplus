import Mathlib
import MathlibPlus.Open.Combinatorics.DTreeUPolynomial

open scoped Classical BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim16071

abbrev UPolynomial := MvPolynomial ℕ ℤ

noncomputable def treeUPolynomial {V : Type*} [Fintype V] [LT V]
    (T : SimpleGraph V) : UPolynomial :=
  MathlibPlus.Open.Combinatorics.DTreeUPolynomial.uPolynomial T

noncomputable def treeM {V : Type*} [Fintype V] [LT V]
    (T : SimpleGraph V) : UPolynomial :=
  MvPolynomial.pderiv 1 (treeUPolynomial T)

noncomputable def deletedGraph {n : ℕ} (T : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : SimpleGraph {v : Fin n // v ∉ C} :=
  T.induce {v | v ∉ C}

noncomputable def connectedVertexSet {n : ℕ} (T : SimpleGraph (Fin n))
    (C : Finset (Fin n)) : Prop :=
  C.Nonempty ∧ (T.induce (C : Set (Fin n))).Connected

noncomputable def connectedSets {n : ℕ} (T : SimpleGraph (Fin n))
    (k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter
    (fun C => C.card = k ∧ connectedVertexSet T C)

noncomputable def branchCoefficientDerivative
    (p : Polynomial UPolynomial) : Polynomial UPolynomial :=
  p.support.sum (fun i =>
    Polynomial.C (MvPolynomial.pderiv 1 (p.coeff i)) * Polynomial.X ^ i)

noncomputable def rootedPruningFactor {V : Type*} [Fintype V] [DecidableEq V] [LT V]
    (B : SimpleGraph V) (r : V) : Polynomial UPolynomial :=
  Finset.sum
    (Finset.filter
      (fun Q : Finset V => Q = ∅ ∨
        ((B.induce (Q : Set V)).Connected ∧ r ∈ Q))
      (Finset.univ : Finset (Finset V)))
    (fun Q : Finset V =>
      Polynomial.C
          (treeUPolynomial (B.induce
            ((↑((Finset.univ : Finset V) \ Q) : Set V)))) *
        Polynomial.X ^ (Fintype.card V - Q.card))

noncomputable def puncturedTree {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) :
    SimpleGraph {v : Fin n // v ≠ c} :=
  T.induce {v | v ≠ c}

abbrev branchIndex {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) :=
  (puncturedTree T c).ConnectedComponent

abbrev branchVertices {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n)
    (i : branchIndex T c) := i.supp

abbrev branchRoots {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) :=
  ∀ i : branchIndex T c, branchVertices T c i

noncomputable def branchGraph {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n)
    (i : branchIndex T c) : SimpleGraph (branchVertices T c i) :=
  (puncturedTree T c).induce i.supp

noncomputable def branchRootsAtCentroid {n : ℕ} (T : SimpleGraph (Fin n))
    (c : Fin n) (r : branchRoots T c) : Prop :=
  ∀ i : branchIndex T c, T.Adj c ((r i).1.1)

noncomputable def branchSubsetVertices {n : ℕ} (T : SimpleGraph (Fin n))
    (c : Fin n) (i : branchIndex T c) (C : Finset (branchVertices T c i)) :
    Set (Fin n) :=
  (fun v : branchVertices T c i => v.1.1) '' (C : Set (branchVertices T c i))

noncomputable def branchDeletionGraph {n : ℕ} (T : SimpleGraph (Fin n))
    (c : Fin n) (i : branchIndex T c)
    (C : Finset (branchVertices T c i)) :
    SimpleGraph {v : Fin n // v ∉ branchSubsetVertices T c i C} :=
  T.induce {v | v ∉ branchSubsetVertices T c i C}

noncomputable def branchConnectedSets {n : ℕ} (T : SimpleGraph (Fin n))
    (c : Fin n) (i : branchIndex T c) (k : ℕ) :
    Finset (Finset (branchVertices T c i)) :=
  (Finset.univ : Finset (Finset (branchVertices T c i))).filter
    (fun C => C.card = k ∧ C.Nonempty ∧
      ((branchGraph T c i).induce (C : Set (branchVertices T c i))).Connected)

noncomputable def branchDeletionMessages {n : ℕ} (T : SimpleGraph (Fin n))
    (c : Fin n) (k : ℕ) : UPolynomial :=
  (Finset.univ : Finset (branchIndex T c)).sum (fun i =>
    (branchConnectedSets T c i k).sum (fun C =>
      treeM (branchDeletionGraph T c i C)))

noncomputable def centroidProduct {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n)
    (r : branchRoots T c) : Polynomial UPolynomial :=
  ∏ i : branchIndex T c,
    rootedPruningFactor (branchGraph T c i) (r i)

noncomputable def uniqueCentroidAt {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) : Prop :=
  ∀ v : Fin n,
    MathlibPlus.Open.Combinatorics.DTreeUPolynomial.centroidVertex T v ↔ v = c

def claim_16071 : Prop :=
  ∀ {n : ℕ} (T : SimpleGraph (Fin n)) (c : Fin n) (r : branchRoots T c),
    T.IsTree →
      uniqueCentroidAt T c →
        branchRootsAtCentroid T c r →
          ∀ k : ℕ,
            MvPolynomial.pderiv k (treeM T) =
              (branchCoefficientDerivative (centroidProduct T c r)).coeff (n - k) +
                branchDeletionMessages T c k

end MathlibPlus.Open.ResearchFormalization.Claim16071
