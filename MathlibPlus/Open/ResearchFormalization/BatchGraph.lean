import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Graph

noncomputable section
open scoped BigOperators

/-- Vertices incident with an unordered edge. -/
def incidentVertices {V : Type*} (e : Sym2 V) : Set V :=
  {v | Sym2.Mem v e}

/-- A finite edge set with pairwise disjoint endpoint sets. -/
def IsMatching {V : Type*} (X : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ X.edgeSet) ∧
    (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
      Disjoint (incidentVertices e) (incidentVertices f))

def matchingFamily {V : Type*} [Fintype V] [Fintype (Sym2 V)] [DecidableEq V]
    (X : SimpleGraph V) (k : ℕ) :=
  {M : Finset (Sym2 V) // M.card = k ∧ IsMatching X M}

def matchingCount {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  letI : DecidablePred
      (fun M : Finset (Sym2 V) => M.card = k ∧ IsMatching X M) :=
    fun M => Classical.propDecidable (M.card = k ∧ IsMatching X M)
  letI : Fintype (matchingFamily X k) :=
    Fintype.subtype
      (Finset.univ.filter (fun M : Finset (Sym2 V) =>
        M.card = k ∧ IsMatching X M))
      (by intro M; simp)
  exact Fintype.card (matchingFamily X k)

def matchingGeneratingPolynomial {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) : Polynomial ℤ :=
  Finset.sum (Finset.range (Fintype.card V + 1)) (fun k =>
    Polynomial.C (matchingCount X k : ℤ) * Polynomial.X ^ k)

def matchingPolynomial {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) : Polynomial ℤ :=
  Finset.sum (Finset.range (Fintype.card V + 1)) (fun k =>
    Polynomial.C ((-1 : ℤ) ^ k * (matchingCount X k : ℤ)) *
      Polynomial.X ^ (Fintype.card V - 2 * k))

def adjacencyMatrix {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) : Matrix V V ℤ := by
  classical
  exact fun v w => if X.Adj v w then 1 else 0

def adjacencyCharacteristicPolynomial {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) : Polynomial ℤ :=
  Matrix.charpoly (adjacencyMatrix X)

def matchingLaurentFormula {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) (n : ℕ) : Prop :=
  let K := FractionRing (Polynomial ℤ)
  let x : K := algebraMap (Polynomial ℤ) K Polynomial.X
  (algebraMap (Polynomial ℤ) K) (matchingPolynomial X) =
    x ^ n *
      Polynomial.eval₂ (algebraMap ℤ K) (-(x⁻¹) ^ 2)
        (matchingGeneratingPolynomial X)

/-- For a forest, the matching polynomial is the characteristic polynomial,
with the displayed `x^n Z_X(-x^-2)` realization. -/
def claim_27574 {V : Type*} [Fintype V] [Fintype (Sym2 V)]
    [Fintype (Finset (Sym2 V))] [DecidableEq V]
    (X : SimpleGraph V) (n : ℕ) : Prop :=
  (X.IsAcyclic ∧ Fintype.card V = n) →
    matchingLaurentFormula X n ∧
      matchingPolynomial X = adjacencyCharacteristicPolynomial X

end

end MathlibPlus.Open.ResearchFormalizationBatch.Graph
