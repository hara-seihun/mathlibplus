import Mathlib
import MathlibPlus.Open.Combinatorics.DTreeUPolynomial
import MathlibPlus.Open.ResearchFormalizationBatch20309

namespace MathlibPlus.Open.Research.FiniteReplayClaim59142

noncomputable section
open Classical
open scoped BigOperators

/-- A finite labeled graph carrier for an order-`n` tree.  Passing to the
`EqvGen` quotient below gives the unlabeled carrier used in the replay. -/
abbrev EdgeSet59142 (n : ℕ) := Finset (Sym2 (Fin n))

def treeGraph59142 {n : ℕ} (E : EdgeSet59142 n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))

def looplessTree59142 {n : ℕ} (E : EdgeSet59142 n) : Prop :=
  (∀ e : Sym2 (Fin n), e ∈ E → ¬e.IsDiag) ∧
    (treeGraph59142 E).IsTree

/-- Graph isomorphism on the finite labeled edge-set carrier. -/
def treeIso59142 {n : ℕ} (E F : EdgeSet59142 n) : Prop :=
  ∃ e : Fin n ≃ Fin n,
    ∀ u v : Fin n,
      (treeGraph59142 E).Adj u v ↔
        (treeGraph59142 F).Adj (e u) (e v)

/-- Unlabeled trees of order `n`, represented using the quotient of the exact
finite edge carrier. -/
abbrev UnlabeledTree59142 (n : ℕ) :=
  Quotient (Relation.EqvGen.setoid (treeIso59142 (n := n)))

noncomputable def labeledTrees59142 (n : ℕ) : Finset (EdgeSet59142 n) :=
  (Finset.univ : Finset (EdgeSet59142 n)).filter looplessTree59142

noncomputable def unlabeledTrees59142 (n : ℕ) :
    Finset (UnlabeledTree59142 n) :=
  (labeledTrees59142 n).image
    (fun E => Quotient.mk (Relation.EqvGen.setoid (treeIso59142 (n := n))) E)

noncomputable def unlabeledTreeCount59142 (n : ℕ) : ℕ :=
  (unlabeledTrees59142 n).card

/-- The centroid classifier is evaluated on the graph represented using a
replayed tree carrier, not on a detached numeral record. -/
def centroidCore59142 {n : ℕ} (E : EdgeSet59142 n) : Set (Fin n) :=
  MathlibPlus.Open.Combinatorics.DTreeUPolynomial.centroidCore
    (treeGraph59142 E)

def centroidCard59142 {n : ℕ} (E : EdgeSet59142 n) : ℕ :=
  (centroidCore59142 E).toFinset.card

def uniqueCentroidTrees59142 (n : ℕ) : Finset (UnlabeledTree59142 n) :=
  (unlabeledTrees59142 n).filter
    (fun T => centroidCard59142 (Quotient.out T) = 1)

def bicentroidTrees59142 (n : ℕ) : Finset (UnlabeledTree59142 n) :=
  (unlabeledTrees59142 n).filter
    (fun T => centroidCard59142 (Quotient.out T) = 2)

def centroidPartition59142 (n : ℕ) : Prop :=
  ∀ T ∈ unlabeledTrees59142 n,
    T ∈ uniqueCentroidTrees59142 n ∨ T ∈ bicentroidTrees59142 n

/-- The actual branch carrier used in the direct centroid-core product. -/
def directBranches59142 {n : ℕ} (E : EdgeSet59142 n) :
    Finset (MathlibPlus.Open.ResearchFormalizationBatch20309.BranchPiece (Fin n)) :=
  (centroidCore59142 E).toFinset.biUnion (fun c =>
    (MathlibPlus.Open.ResearchFormalizationBatch20309.childBranches
      (treeGraph59142 E) c).filter
      (fun B => B.root ∉ centroidCore59142 E))

def directCentroidProduct59142 {n : ℕ} (E : EdgeSet59142 n) :
    MathlibPlus.Open.ResearchFormalizationBatch20309.RootedPolynomial :=
  ∏ B ∈ directBranches59142 E,
    MathlibPlus.Open.ResearchFormalizationBatch20309.rootedFactorOnBranch
      (treeGraph59142 E) B

/-- The strict-giant coefficient extracted from the exact finite U-polynomial. -/
def strictGiantCoefficient59142 (n j : ℕ) (E : EdgeSet59142 n) :
    MvPolynomial ℕ ℤ :=
  MvPolynomial.pderiv (n - j)
    (MathlibPlus.Open.Combinatorics.DTreeUPolynomial.uPolynomial
      (treeGraph59142 E))

def directProductCoefficient59142 (j : ℕ) {n : ℕ} (E : EdgeSet59142 n) :
    MvPolynomial ℕ ℤ :=
  (directCentroidProduct59142 E).coeff j

/-- One checked strict-giant coefficient/product row on an unlabeled tree. -/
def strictGiantIdentity59142 (n j : ℕ) (T : UnlabeledTree59142 n) : Prop :=
  strictGiantCoefficient59142 n j (Quotient.out T) =
    directProductCoefficient59142 j (Quotient.out T)

def strictGiantRows59142 (n : ℕ) (T : UnlabeledTree59142 n) : Finset ℕ :=
  (Finset.range ((n + 1) / 2)).filter
    (fun j => strictGiantIdentity59142 n j T)

def auditedOrders59142 : Finset ℕ := Finset.Icc 1 12

/-- The replay's 5,652-row count is computed from the tree carrier and its
strict-prefix index range. -/
def strictGiantIdentityCount59142 : ℕ :=
  ∑ n ∈ auditedOrders59142,
    ∑ T ∈ unlabeledTrees59142 n, (strictGiantRows59142 n T).card

def allStrictGiantRows59142 : Prop :=
  ∀ n ∈ auditedOrders59142,
    ∀ T ∈ unlabeledTrees59142 n,
      ∀ j ∈ Finset.range ((n + 1) / 2),
        strictGiantIdentity59142 n j T

/-- The direct product degree and unit-normalization checks retained in the
finite replay. -/
def directProductDegree59142 (n : ℕ) (T : UnlabeledTree59142 n) : ℕ :=
  (directCentroidProduct59142 (Quotient.out T)).natDegree

def directProductDegreeAudit59142 : Prop :=
  ∀ n ∈ auditedOrders59142,
    ∀ T ∈ unlabeledTrees59142 n,
      directProductDegree59142 n T =
        n - centroidCard59142 (Quotient.out T) ∧
      (directCentroidProduct59142 (Quotient.out T)).coeff 0 = 1

/-- The strict-prefix product map whose fibers are audited, with its exact
fiber equivalence relation made explicit. -/
def strictPrefixProductMap59142 (n : ℕ) (T : UnlabeledTree59142 n) :
    Fin ((n + 1) / 2) → MvPolynomial ℕ ℤ :=
  fun j => directProductCoefficient59142 j (Quotient.out T)

def strictPrefixEquivalent59142 (n : ℕ)
    (T T' : UnlabeledTree59142 n) : Prop :=
  strictPrefixProductMap59142 n T = strictPrefixProductMap59142 n T'

abbrev strictPrefixFiberQuotient59142 (n : ℕ) :=
  Quotient (Relation.EqvGen.setoid (strictPrefixEquivalent59142 n))

noncomputable def strictPrefixFiberClass59142
    (n : ℕ) (T : UnlabeledTree59142 n) : strictPrefixFiberQuotient59142 n :=
  Quotient.mk (Relation.EqvGen.setoid (strictPrefixEquivalent59142 n)) T

noncomputable def strictPrefixFiberClasses59142 (n : ℕ) :
    Finset (strictPrefixFiberQuotient59142 n) :=
  (unlabeledTrees59142 n).image (strictPrefixFiberClass59142 n)

noncomputable def strictPrefixFiberCard59142
    (n : ℕ) (F : strictPrefixFiberQuotient59142 n) : ℕ :=
  ((unlabeledTrees59142 n).filter
    (fun T => strictPrefixFiberClass59142 n T = F)).card

noncomputable def collidingStrictPrefixFibers59142 (n : ℕ) :
    Finset (strictPrefixFiberQuotient59142 n) :=
  (strictPrefixFiberClasses59142 n).filter
    (fun F => strictPrefixFiberCard59142 n F > 1)

/-- Quotient equality and equality of the strict-prefix product map are the
same fiber relation used in the census. -/
def strictPrefixFiberEquivalence59142 (n : ℕ) : Prop :=
  ∀ T T' : UnlabeledTree59142 n,
    strictPrefixFiberClass59142 n T = strictPrefixFiberClass59142 n T' ↔
      strictPrefixEquivalent59142 n T T'

def strictPrefixCollisionFiberCount59142 : ℕ :=
  ∑ n ∈ auditedOrders59142,
    (collidingStrictPrefixFibers59142 n).card

def treesInCollidingStrictPrefixFibers59142 : ℕ :=
  ∑ n ∈ auditedOrders59142,
    ∑ F ∈ collidingStrictPrefixFibers59142 n,
      strictPrefixFiberCard59142 n F

/-- Claim 59142: the finite replay is the explicit edge-carrier/quotient
certificate through order twelve.  It records the centroid partition, every
strict-giant coefficient/product row, the product-degree normalization, and
the strict-prefix fiber census.  This is deliberately a bounded audit; it
contains no all-order conclusion and does not close the global divisor
obligation. -/
def claim59142_finiteReplayAudit : Prop :=
  (∑ n ∈ auditedOrders59142, unlabeledTreeCount59142 n) = 987 ∧
    (∑ n ∈ auditedOrders59142,
      (uniqueCentroidTrees59142 n).card) = 717 ∧
    (∑ n ∈ auditedOrders59142,
      (bicentroidTrees59142 n).card) = 270 ∧
    (∀ n ∈ auditedOrders59142, centroidPartition59142 n) ∧
    allStrictGiantRows59142 ∧
    strictGiantIdentityCount59142 = 5652 ∧
    directProductDegreeAudit59142 ∧
    (∀ n ∈ auditedOrders59142, strictPrefixFiberEquivalence59142 n) ∧
    strictPrefixCollisionFiberCount59142 = 63 ∧
    treesInCollidingStrictPrefixFibers59142 = 126

end

end MathlibPlus.Open.Research.FiniteReplayClaim59142
