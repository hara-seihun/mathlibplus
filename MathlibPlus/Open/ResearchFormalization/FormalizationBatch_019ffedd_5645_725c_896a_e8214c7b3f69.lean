import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- A finite simple graph on `Fin n`, encoded by its Boolean adjacency matrix. -/
abbrev GraphCode (n : ℕ) :=
  {a : Fin n → Fin n → Bool //
    (∀ u v, a u v = a v u) ∧ ∀ u, a u u = false}

def graphCodeIso {n : ℕ} (G H : GraphCode n) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ u v, G.1 u v = H.1 (e u) (e v)

instance graphCodeSetoid (n : ℕ) : Setoid (GraphCode n) where
  r := graphCodeIso
  iseqv :=
    { refl := by
        intro G
        exact ⟨Equiv.refl _, by simp⟩
      symm := by
        intro G H h
        rcases h with ⟨e, h⟩
        refine ⟨e.symm, ?_⟩
        intro u v
        have huv := h (e.symm u) (e.symm v)
        simpa using huv.symm
      trans := by
        intro G H K hGH hHK
        rcases hGH with ⟨e, he⟩
        rcases hHK with ⟨f, hf⟩
        refine ⟨e.trans f, ?_⟩
        intro u v
        simp [Equiv.trans_apply, he, hf] }

abbrev GraphType (n : ℕ) := Quotient (graphCodeSetoid n)

noncomputable instance graphTypeFintype (n : ℕ) : Fintype (GraphType n) :=
  Fintype.ofFinite _

def graphRepresentative {n : ℕ} (X : GraphType n) : GraphCode n :=
  Quotient.out X

noncomputable def unorderedPairs (n : ℕ) : Finset (Fin n × Fin n) := by
  classical
  exact (Finset.univ.product Finset.univ).filter (fun e => e.1 < e.2)

noncomputable def graphEdges {n : ℕ} (G : GraphCode n) : Finset (Fin n × Fin n) := by
  classical
  exact (unorderedPairs n).filter (fun e => G.1 e.1 e.2 = true)

def disjointEdgeEndpoints {n : ℕ} (e f : Fin n × Fin n) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

def isMatching {n : ℕ} (M : Finset (Fin n × Fin n)) : Prop :=
  ∀ ⦃e f : Fin n × Fin n⦄, e ∈ M → f ∈ M → e ≠ f → disjointEdgeEndpoints e f

noncomputable def matchingSets (n q : ℕ) : Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (unorderedPairs n).powerset.filter (fun M => M.card = q ∧ isMatching M)

noncomputable def signedMatchingCharacter (n q : ℕ) (G : GraphCode n) : ℤ :=
  (-1 : ℤ) ^ (graphEdges G).card *
    ∑ M ∈ matchingSets n q, (-1 : ℤ) ^ (M ∩ graphEdges G).card

/-- Claim 22886: the signed matching character, with all matchings taken on the
complete vertex set and the graph contributing through the intersection sign. -/
def claim_22886 (n q : ℕ) (G : GraphCode n) : Prop :=
  q ≤ n / 2 →
    signedMatchingCharacter n q G =
      (-1 : ℤ) ^ (graphEdges G).card *
        ∑ M ∈ matchingSets n q, (-1 : ℤ) ^ (M ∩ graphEdges G).card

def graphAutomorphisms {n : ℕ} (G : GraphCode n) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter (fun e => ∀ u v, G.1 u v = G.1 (e u) (e v))

def graphAutomorphismOrder {n : ℕ} (G : GraphCode n) : ℕ :=
  (graphAutomorphisms G).card

abbrev GraphVector (K : Type*) [Zero K] (n : ℕ) := GraphType n →₀ K

def orbitWeightedMatchingVector (K : Type*) [Field K] (n q : ℕ) : GraphVector K n :=
  ∑ X : GraphType n,
    (((Nat.factorial n : K) /
        (graphAutomorphismOrder (graphRepresentative X) : K)) *
      (signedMatchingCharacter n q (graphRepresentative X) : K)) •
      Finsupp.single X (1 : K)

def matchingSubspace (K : Type*) [Field K] (n : ℕ) : Submodule K (GraphVector K n) :=
  Submodule.span K
    (Set.range (fun q : Fin (n / 2 + 1) =>
      orbitWeightedMatchingVector K n q.1))

/-- Claim 22887: the orbit-weighted matching vector and its matching span. -/
def claim_22887 (n q : ℕ) : Prop :=
  q ≤ n / 2 →
    orbitWeightedMatchingVector ℚ n q =
      ∑ X : GraphType n,
        (((Nat.factorial n : ℚ) /
            (graphAutomorphismOrder (graphRepresentative X) : ℚ)) *
          (signedMatchingCharacter n q (graphRepresentative X) : ℚ)) •
          Finsupp.single X (1 : ℚ)
    ∧ matchingSubspace ℚ n =
      Submodule.span ℚ
        (Set.range (fun r : Fin (n / 2 + 1) =>
          orbitWeightedMatchingVector ℚ n r.1))

def oldIndex {n : ℕ} (i : Fin (n + 1)) : Option (Fin n) :=
  if h : i.val < n then some ⟨i.val, h⟩ else none

def adjoinAdj {n : ℕ} (G : GraphCode n) (S : Finset (Fin n))
    (i j : Fin (n + 1)) : Bool :=
  match oldIndex i, oldIndex j with
  | some u, some v => G.1 u v
  | none, some v => decide (v ∈ S)
  | some u, none => decide (u ∈ S)
  | none, none => false

def adjoinGraph {n : ℕ} (G : GraphCode n) (S : Finset (Fin n)) : GraphCode (n + 1) := by
  classical
  refine ⟨adjoinAdj G S, ?_, ?_⟩
  · intro i j
    by_cases hi : oldIndex i = none
    · by_cases hj : oldIndex j = none
      · simp [adjoinAdj, hi, hj]
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hj
        simp [adjoinAdj, hi, hj, hv]
    · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hi
      by_cases hj : oldIndex j = none
      · simp [adjoinAdj, hi, hu, hj]
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hj
        simp [adjoinAdj, hi, hu, hj, hv, G.2.1]
  · intro i
    by_cases hi : oldIndex i = none
    · simp [adjoinAdj, hi]
    · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hi
      simp [adjoinAdj, hi, hu, G.2.2]

noncomputable def insertionBasis {K : Type*} [Field K]
    (n d : ℕ) (X : GraphType n) : GraphVector K (n + 1) := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = d),
    Finsupp.single (Quotient.mk (graphCodeSetoid (n + 1))
      (adjoinGraph (graphRepresentative X) S)) (1 : K)

def insertionOperator {K : Type*} [Field K]
    (n d : ℕ) : GraphVector K n →ₗ[K] GraphVector K (n + 1) :=
  Finsupp.lsum K (fun X =>
    LinearMap.smulRight (LinearMap.id) (insertionBasis n d X))

noncomputable def alternatingInsertion {K : Type*} [Field K]
    (n : ℕ) : GraphVector K n →ₗ[K] GraphVector K (n + 1) :=
  ∑ d ∈ Finset.range (n + 1), ((-1 : K) ^ d) • insertionOperator n d

/-- Claim 22888: alternating full-star insertion is the signed sum of the
operators indexed by the size of the new vertex's neighborhood. -/
def claim_22888 {K : Type*} [Field K] (n : ℕ) : Prop :=
  alternatingInsertion (K := K) n =
    ∑ d ∈ Finset.range (n + 1), ((-1 : K) ^ d) • insertionOperator (K := K) n d

/-- Claim 22889: the alternating insertion intertwines the matching vectors. -/
def claim_22889 {K : Type*} [Field K] [CharZero K] (n q : ℕ) : Prop :=
  q ≤ n / 2 →
    alternatingInsertion n (orbitWeightedMatchingVector K n q) =
      (((n + 1 - 2 * q : ℕ) : K) / (n + 1 : K)) •
        orbitWeightedMatchingVector K (n + 1) q

/-- Claim 22890: the nonzero diagonal factors make alternating insertion
injective after restriction to the matching subspace. -/
def claim_22890 {K : Type*} [Field K] [CharZero K] (n : ℕ) : Prop :=
  (∀ q : ℕ, q ≤ n / 2 → ((n + 1 - 2 * q : ℕ) : K) ≠ 0) ∧
    Function.Injective (fun v : matchingSubspace K n =>
      alternatingInsertion n v.1)

def deleteGraph {n : ℕ} (G : GraphCode (n + 1)) (v : Fin (n + 1)) : GraphCode n :=
  ⟨fun i j => G.1 (Fin.succAbove v i) (Fin.succAbove v j),
    by intro i j; simpa using G.2.1 (Fin.succAbove v i) (Fin.succAbove v j),
    by intro i; exact G.2.2 _⟩

def vertexDegree {n : ℕ} (G : GraphCode n) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun u => G.1 v u = true)).card

noncomputable def deletionBasis {K : Type*} [Field K]
    (n d : ℕ) (X : GraphType (n + 1)) : GraphVector K n := by
  classical
  exact ∑ v ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun v => vertexDegree (graphRepresentative X) v = d),
    Finsupp.single (Quotient.mk (graphCodeSetoid n)
      (deleteGraph (graphRepresentative X) v)) (1 : K)

def deletionOperator {K : Type*} [Field K]
    (n d : ℕ) : GraphVector K (n + 1) →ₗ[K] GraphVector K n :=
  Finsupp.lsum K (fun X =>
    LinearMap.smulRight (LinearMap.id) (deletionBasis n d X))

def matchingVectorAtInteger {K : Type*} [Field K]
    (n : ℕ) (q : ℤ) : GraphVector K n :=
  if q < 0 then 0 else orbitWeightedMatchingVector K n q.toNat

def choosePreviousRow (n d : ℕ) : ℕ :=
  Nat.choose (n - 1) d

def choosePreviousDiagonal (n d : ℕ) : ℕ :=
  if d = 0 then 0 else Nat.choose (n - 1) (d - 1)

/-- Claim 22891: degree-marked deletion has the stated matching-vector
intertwining formula, with the negative-index convention made explicit. -/
def claim_22891 {K : Type*} [Field K] (n q d : ℕ) : Prop :=
  q ≤ (n + 1) / 2 →
    matchingVectorAtInteger (K := K) n (-1) = 0 ∧
    deletionOperator (K := K) n d (orbitWeightedMatchingVector K (n + 1) q) =
      (((n + 1 : ℕ) : K) * (-1 : K) ^ d) •
        ( ((Nat.choose n d : ℕ) : K) • matchingVectorAtInteger (K := K) n (q : ℤ) +
          (((((n : ℤ) - 2 * (q : ℤ) + 2 : ℤ) : K) *
              (((choosePreviousRow n d : ℕ) : K) -
                ((choosePreviousDiagonal n d : ℕ) : K))) •
            matchingVectorAtInteger (K := K) n ((q : ℤ) - 1)))

def endpointDeletionPair {K : Type*} [Field K]
    (n : ℕ) (v : GraphVector K (n + 1)) : GraphVector K n × GraphVector K n :=
  (deletionOperator (K := K) n 0 v, deletionOperator (K := K) n n v)

/-- Claim 22893: the degree-zero and degree-n deletion components are jointly
injective on the order-n+1 matching subspace. -/
def claim_22893 {K : Type*} [Field K] [CharZero K] (n : ℕ) : Prop :=
  Function.Injective (fun v : matchingSubspace K (n + 1) =>
    endpointDeletionPair (K := K) n v.1)

abbrev CorePolynomial := MvPolynomial (Fin 6) ℚ

def coreVar (i : Fin 6) : CorePolynomial := MvPolynomial.X i

def coreX0 : CorePolynomial := coreVar 0
def coreX1 : CorePolynomial := coreVar 1
def coreX2 : CorePolynomial := coreVar 2
def coreY0 : CorePolynomial := coreVar 3
def coreY1 : CorePolynomial := coreVar 4
def coreY2 : CorePolynomial := coreVar 5

def coreSourcePolynomialSet : Set CorePolynomial :=
  {6 * coreX1,
    2 * (coreX0 + coreX2),
    12 * coreX1 ^ 2,
    2 * (coreY0 + coreY2 + coreX0 * coreX2),
    coreX0 ^ 2 + coreX2 ^ 2 + 2 * (coreX0 * coreX1 + coreX1 * coreX2 + coreY1)}

def coreSourceIdeal : Ideal CorePolynomial :=
  Ideal.span coreSourcePolynomialSet

abbrev CoreQuotient := CorePolynomial ⧸ coreSourceIdeal

def coreQuotientVar (i : Fin 6) : CoreQuotient :=
  Ideal.Quotient.mk coreSourceIdeal (coreVar i)

/-- Claim 22913: the fixed-core quotient, with its four displayed coordinate
reductions and its infinite-dimensional consequence. -/
def claim_22913 : Prop :=
  Nonempty (CoreQuotient ≃ₐ[ℚ] MvPolynomial (Fin 2) ℚ) ∧
    coreQuotientVar 1 = 0 ∧
    coreQuotientVar 2 = -coreQuotientVar 0 ∧
    coreQuotientVar 4 = -(coreQuotientVar 0 ^ 2) ∧
    coreQuotientVar 5 = coreQuotientVar 0 ^ 2 - coreQuotientVar 3 ∧
    ¬FiniteDimensional ℚ CoreQuotient

abbrev DegreeTwoVector := Fin 6 → ℚ

def degreeTwoGenerators : Set DegreeTwoVector :=
  {![1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 2, 0, 0],
    ![12, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 2],
    ![0, 2, 1, 0, 2, 0]}

def degreeTwoSpan : Submodule ℚ DegreeTwoVector :=
  Submodule.span ℚ degreeTwoGenerators

def degreeTwoFunctional (v : DegreeTwoVector) : ℚ :=
  -2 * v 2 + v 3 + v 4 - v 5

/-- Claim 22914: the explicit reversal-invariant degree-two span has codimension
one, and the displayed coordinate functional detects its cokernel. -/
def claim_22914 : Prop :=
  Module.finrank ℚ degreeTwoSpan = 5 ∧
    Module.finrank ℚ (DegreeTwoVector ⧸ degreeTwoSpan) = 1 ∧
    (∃ v : DegreeTwoVector, degreeTwoFunctional v ≠ 0) ∧
    (∀ v : DegreeTwoVector, v ∈ degreeTwoSpan → degreeTwoFunctional v = 0)

end MathlibPlus.Open.ResearchFormalization.Batch
