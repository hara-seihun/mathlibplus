import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch

/-! Common finite-set formulations for the fixed-intersection claims. -/

def uniformFamily {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ A ∈ 𝓕, A.card = n

def lIntersecting {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (L : Finset ℕ) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ≠ B → (A ∩ B).card ∈ L

def threePetalSunflower {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ∃ A B C : Finset α,
    A ∈ 𝓕 ∧ B ∈ 𝓕 ∧ C ∈ 𝓕 ∧
    A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
    A ∩ B = A ∩ C ∧ A ∩ C = B ∩ C

def sunflowerFree {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : Prop :=
  ¬ threePetalSunflower 𝓕

def constantIntersection {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) (ℓ : ℕ) : Prop :=
  ∀ ⦃A B : Finset α⦄, A ∈ 𝓕 → B ∈ 𝓕 → A ≠ B → (A ∩ B).card = ℓ

def claim35168_exactFixedIntersectionSpectrum
    (α : Type*) [DecidableEq α] (n s : ℕ) (L : Finset ℕ)
    (𝓕 : Finset (Finset α)) : Prop :=
  L.card = s ∧
  uniformFamily 𝓕 n ∧
  lIntersecting 𝓕 L ∧
  sunflowerFree 𝓕

def claim35169_fixedSpectrumSunflowerBound
    (α : Type*) [DecidableEq α] (n s : ℕ) (L : Finset ℕ)
    (𝓕 : Finset (Finset α)) : Prop :=
  (L.card = s ∧ uniformFamily 𝓕 n ∧ lIntersecting 𝓕 L ∧ sunflowerFree 𝓕) →
    (𝓕.card : ℝ) ≤
      ((n ^ 2 - n + 2 : ℕ) : ℝ) *
        (8 : ℝ) ^ (s - 1) *
        Real.rpow (2 : ℝ)
          (((1 : ℝ) + Real.sqrt 5 / 5) * (n : ℝ) * ((s - 1 : ℕ) : ℝ))

def claim35170_constantIntersectionBaseCase
    (α : Type*) [DecidableEq α] (n ℓ : ℕ)
    (𝓕 : Finset (Finset α)) : Prop :=
  (uniformFamily 𝓕 n ∧ constantIntersection 𝓕 ℓ) →
    ((threePetalSunflower 𝓕 ∨
        (𝓕.card : ℝ) ≤ ((n ^ 2 - n + 1 : ℕ) : ℝ)) ∧
      (sunflowerFree 𝓕 →
        (𝓕.card : ℝ) ≤ ((n ^ 2 - n + 2 : ℕ) : ℝ)))

/-! The indexed residual occurrence and residual-hypergraph formulations. -/

def indexedThreeSunflowerFree {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) : Prop :=
  ∀ ⦃i j k : Fin m⦄,
    i ≠ j → i ≠ k → j ≠ k →
      ¬ (A i ∩ A j = A i ∩ A k ∧ A i ∩ A k = A j ∩ A k)

def residualOccurrence {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (Y : Finset α) (i : Fin m) : Finset α :=
  A i \ Y

def residualTripleEdge {α : Type*} [DecidableEq α] {m : ℕ}
    (B : Fin m → Finset α) (i j k : Fin m) : Prop :=
  i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    B i ∩ B j = B i ∩ B k ∧ B i ∩ B k = B j ∩ B k

def residualHyperedge {α : Type*} [DecidableEq α] {m : ℕ}
    (B : Fin m → Finset α) (e : Finset (Fin m)) : Prop :=
  e.card = 3 ∧
    ∃ i j k : Fin m, e = {i, j, k} ∧ residualTripleEdge B i j k

noncomputable def residualHypergraph {α : Type*} [DecidableEq α] {m : ℕ}
    (B : Fin m → Finset α) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (residualHyperedge B)

def residualEdgeCount {α : Type*} [DecidableEq α] {m : ℕ}
    (B : Fin m → Finset α) : ℕ :=
  (residualHypergraph B).card

def sourceTripleSunflower {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (i j k : Fin m) : Prop :=
  A i ∩ A j = A i ∩ A k ∧ A i ∩ A k = A j ∩ A k

def occursExactlyTwo {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (y : α) (i j k : Fin m) : Prop :=
  (if y ∈ A i then 1 else 0) +
      (if y ∈ A j then 1 else 0) +
      (if y ∈ A k then 1 else 0) = 2

def claim36764_literalRegularDeletedLayer
    (α : Type*) [DecidableEq α] (m r p s n : ℕ)
    (A : Fin m → Finset α) (Y : Finset α) : Prop :=
  Function.Injective A ∧
  (∀ i, (A i).card = r) ∧
  indexedThreeSunflowerFree A ∧
  (∀ i, (A i ∩ Y).card = p) ∧
  (∀ y ∈ Y, (Finset.univ.filter (fun i : Fin m => y ∈ A i)).card ≤ s) ∧
  n = r - p ∧
  (∀ i, (residualOccurrence A Y i).card = n)

def claim36765_residualSunflowerHypergraph
    (α : Type*) [DecidableEq α] (m : ℕ)
    (A : Fin m → Finset α) (Y : Finset α)
    (B : Fin m → Finset α) : Prop :=
  (∀ i, B i = residualOccurrence A Y i) ∧
  indexedThreeSunflowerFree A ∧
  (∀ ⦃i j k : Fin m⦄, residualTripleEdge B i j k →
    (¬ sourceTripleSunflower A i j k ∧
      ∃ y : α, y ∈ Y ∧ occursExactlyTwo A y i j k))

def memberDegree {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (y : α) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => y ∈ A i)).card

noncomputable def tripleWitnessCount {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) (y : α) : ℕ := by
  classical
  exact Fintype.card
    {e : Finset (Fin m) //
      e.card = 3 ∧ (e.filter (fun i : Fin m => y ∈ A i)).card = 2}

def claim36766_exactWitnessEdgeCount
    (α : Type*) [DecidableEq α] (m r p s : ℕ)
    (A : Fin m → Finset α) (Y : Finset α)
    (B : Fin m → Finset α) : Prop :=
  (∀ i, B i = residualOccurrence A Y i) ∧
  indexedThreeSunflowerFree A ∧
  (∀ y ∈ Y,
    tripleWitnessCount A y =
      Nat.choose (memberDegree A y) 2 * (m - memberDegree A y)) ∧
  residualEdgeCount B ≤
    ∑ y ∈ Y, Nat.choose (memberDegree A y) 2 * (m - memberDegree A y) ∧
  ((∀ y ∈ Y, memberDegree A y ≤ s) →
    (∑ y ∈ Y, memberDegree A y = m * p) →
      (residualEdgeCount B : ℚ) ≤
        (((s - 1 : ℕ) : ℚ) * (p : ℚ) / 2) * (m : ℚ) ^ 2)

def isThreeUniformHypergraph {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

def independentSet {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (I : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ I

def isIndependenceNumber {V : Type*} [DecidableEq V]
    (H : Finset (Finset V)) (a : ℕ) : Prop :=
  (∃ I : Finset V, independentSet H I ∧ I.card = a) ∧
    ∀ I : Finset V, independentSet H I → I.card ≤ a

def claim36767_independenceTransfer
    (V : Type*) [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) : Prop :=
  isThreeUniformHypergraph H ∧
  ∃ a : ℕ, isIndependenceNumber H a ∧
    (∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      ∃ I : Finset V,
        independentSet H I ∧
        (I.card : ℝ) ≥
          z * (Fintype.card V : ℝ) - z ^ 3 * (H.card : ℝ)) ∧
    (((H.card : ℝ) ≥ (Fintype.card V : ℝ) / 3) →
      (∃ I : Finset V,
        independentSet H I ∧
        (I.card : ℝ) ≥
          Real.sqrt ((Fintype.card V : ℝ) / (3 * (H.card : ℝ))) *
              (Fintype.card V : ℝ) -
            (Real.sqrt ((Fintype.card V : ℝ) / (3 * (H.card : ℝ))) : ℝ) ^ 3 *
              (H.card : ℝ)) ∧
      (a : ℝ) ≥
        (2 / (3 * Real.sqrt 3)) *
          Real.rpow (Fintype.card V : ℝ) (3 / 2) /
            Real.sqrt (H.card : ℝ)) ∧
    (((H.card : ℝ) < (Fintype.card V : ℝ) / 3) →
      (∃ I : Finset V,
        independentSet H I ∧
        (I.card : ℝ) ≥ (Fintype.card V : ℝ) - (H.card : ℝ)) ∧
      (a : ℝ) ≥ (Fintype.card V : ℝ) - (H.card : ℝ) ∧
      (Fintype.card V : ℝ) - (H.card : ℝ) >
        2 * (Fintype.card V : ℝ) / 3)

def claim36768_oneStepResidualIndependenceTransfer
    (α : Type*) [DecidableEq α] (m s p : ℕ)
    (B : Fin m → Finset α) (a : ℕ) : Prop :=
  isThreeUniformHypergraph (residualHypergraph B) ∧
  isIndependenceNumber (residualHypergraph B) a ∧
  (residualEdgeCount B : ℚ) ≤
    (((s - 1 : ℕ) : ℚ) * (p : ℚ) / 2) * (m : ℚ) ^ 2 →
  ((m : ℝ) ≤
      max ((3 / 2 : ℝ) * (a : ℝ))
        ((27 / 8 : ℝ) * ((s - 1 : ℕ) : ℝ) * (p : ℝ) * (a : ℝ) ^ 2)) ∧
    ((s = 1 ∨ p = 0) → residualEdgeCount B = 0 ∧ a = m)

/-! The discrete orthogonal-polynomial contradiction. -/

def supportSignChangeCount {N : ℕ} (v : Fin N → ℝ) : ℕ := by
  classical
  let values : List ℝ := List.ofFn v
  let nonzero := values.filter (fun t => t ≠ 0)
  exact (nonzero.zipWith
      (fun a b : ℝ => if a * b < 0 then 1 else 0) nonzero.tail).sum

def claim8946_signChangePolynomialContradiction : Prop :=
  ∀ (N n : ℕ) (x w : Fin N → ℝ) (p : Polynomial ℝ),
    StrictMono x →
    (∀ i, 0 < w i) →
    p.Monic →
    p.natDegree = n →
    (∀ q : Polynomial ℝ, q.natDegree < n →
      (∑ i : Fin N, w i * p.eval (x i) * q.eval (x i)) = 0) →
    supportSignChangeCount (fun i => p.eval (x i)) < n →
    ∃ q : Polynomial ℝ,
      q.natDegree < n ∧
      0 < (∑ i : Fin N, w i * p.eval (x i) * q.eval (x i))

/-! Boolean-cube notation for the common- and directionwise-unate claims. -/

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev DirectionDomain (n : ℕ) (i : Fin n) := {x : Cube n // x i = false}

def cubeAdd {n : ℕ} (x σ : Cube n) : Cube n :=
  fun i => if x i = σ i then false else true

def extendDirection {n : ℕ} (i : Fin n)
    (f : DirectionDomain n i → Bool) (x : Cube n) : Bool :=
  f ⟨Function.update x i false, by simp⟩

def directionValue {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool)
    (i : Fin n) (x : Cube n) : Bool :=
  extendDirection i (f i) x

def coordinateIncreasing {n : ℕ} (h : Cube n → Bool) (j : Fin n) : Prop :=
  ∀ x, h x = true → h (Function.update x j true) = true

def coordinateDecreasing {n : ℕ} (h : Cube n → Bool) (j : Fin n) : Prop :=
  ∀ x, h (Function.update x j true) = true → h x = true

def increasingNormalization {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  ∀ i j, i ≠ j → coordinateIncreasing (directionValue f i) j

def globallyUnate {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  ∃ σ : Cube n,
    ∀ i j, i ≠ j →
      coordinateIncreasing (fun x => directionValue f i (cubeAdd x σ)) j

def directionwiseUnate {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  ∃ sign : Fin n → Fin n → Bool,
    ∀ i j, i ≠ j →
      ((sign i j = true ∧ coordinateIncreasing (directionValue f i) j) ∨
        (sign i j = false ∧ coordinateDecreasing (directionValue f i) j))

def selectedCubeEdge {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool)
    (x y : Cube n) : Prop :=
  ∃ i : Fin n,
    x i = false ∧ y i = true ∧
    (∀ k, k ≠ i → x k = y k) ∧ directionValue f i x = true

def cubeAdjacency {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool)
    (x y : Cube n) : Prop :=
  selectedCubeEdge f x y ∨ selectedCubeEdge f y x

def cycleNext {k : ℕ} (i : Fin k) : Fin k :=
  if h : i.val + 1 < k then
    ⟨i.val + 1, h⟩
  else
    ⟨0, by omega⟩

def containsCycle {V : Type*} (E : V → V → Prop) : Prop :=
  ∃ k : ℕ, 3 ≤ k ∧ ∃ v : Fin k → V,
    Function.Injective v ∧ ∀ i, E (v i) (v (cycleNext i))

def isForest {V : Type*} (E : V → V → Prop) : Prop :=
  ¬ containsCycle E

def isC4Free {V : Type*} (E : V → V → Prop) : Prop :=
  ¬ ∃ a b c d : V,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    E a b ∧ E b c ∧ E c d ∧ E d a

def coordinateSquare {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool)
    (i j : Fin n) (x : Cube n) : Prop :=
  x i = false ∧ x j = false ∧
    cubeAdjacency f x (Function.update x i true) ∧
    cubeAdjacency f x (Function.update x j true) ∧
    cubeAdjacency f (Function.update x i true)
      (Function.update (Function.update x i true) j true) ∧
    cubeAdjacency f (Function.update x j true)
      (Function.update (Function.update x j true) i true)

def claim36905_literalDirectionalEdgeFunctionsAndCommonUnateness
    (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  globallyUnate f

def claim36908_globallyUnateC4FreeGraphsAreForests
    (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  globallyUnate f →
    (isC4Free (cubeAdjacency f) ↔ isForest (cubeAdjacency f))

noncomputable def directionCount {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) (i : Fin n) : ℕ := by
  classical
  exact Fintype.card
    {x : Cube n // x i = false ∧ directionValue f i x = true}

def selectedEdgeCount {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) : ℕ :=
  ∑ i : Fin n, directionCount f i

def directionDensity {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) (i : Fin n) : ℝ :=
  (directionCount f i : ℝ) / (2 ^ (n - 1) : ℕ)

def claim36910_sharpEdgeAndDensityBounds
    (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  (isForest (cubeAdjacency f) →
    selectedEdgeCount f ≤ 2 ^ n - 1) ∧
  (globallyUnate f → isC4Free (cubeAdjacency f) →
    selectedEdgeCount f ≤ 2 ^ n - 1 ∧
    (∑ i : Fin n, directionDensity f i) =
      (selectedEdgeCount f : ℝ) / (2 ^ (n - 1) : ℕ) ∧
    (selectedEdgeCount f : ℝ) / (2 ^ (n - 1) : ℕ) ≤
      2 - (2 : ℝ) / (2 ^ n : ℕ))

def inForcedZeroSet {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool)
    (i j : Fin n) : Prop :=
  j ≠ i ∧ ∀ x : Cube n,
    x i = false → x j = false → directionValue f i x = false

noncomputable def forcedZeroSet {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (inForcedZeroSet f i)

def claim36912_forcedZeroLowerSlices
    (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  (increasingNormalization f ∧ isC4Free (cubeAdjacency f) →
    ∀ i j, i ≠ j → inForcedZeroSet f i j ∨ inForcedZeroSet f j i) ∧
  (increasingNormalization f →
    ∀ i j, i ≠ j →
      (¬ inForcedZeroSet f i j ∧ ¬ inForcedZeroSet f j i) →
        ∃ x : Cube n, coordinateSquare f i j x)

def isTournament {n : ℕ} (T : Fin n → Fin n → Bool) : Prop :=
  (∀ i, T i i = false) ∧
  ∀ ⦃i j : Fin n⦄, i ≠ j →
    ((T i j = true ∧ T j i = false) ∨
      (T i j = false ∧ T j i = true))

def tournamentOutdegree {n : ℕ} (T : Fin n → Fin n → Bool) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => T i j = true)).card

def selectedProbability {n : ℕ}
    (f : (i : Fin n) → DirectionDomain n i → Bool) (i : Fin n) : ℝ :=
  (Fintype.card {x : Cube n // directionValue f i x = true} : ℝ) /
    (2 ^ n : ℕ)

def claim36913_tournamentEncodingAndProbabilityBound
    (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  increasingNormalization f ∧
  (∀ i j, i ≠ j → inForcedZeroSet f i j ∨ inForcedZeroSet f j i) →
    ∃ T : Fin n → Fin n → Bool,
      isTournament T ∧
      (∀ i j, T i j = true → inForcedZeroSet f i j) ∧
      (∀ i, tournamentOutdegree T i ≤ (forcedZeroSet f i).card) ∧
      (∀ i, ∀ x : Cube n, directionValue f i x = true →
        ∀ j ∈ forcedZeroSet f i, x j = true) ∧
      (∀ i,
        selectedProbability f i ≤
          (1 : ℝ) / (2 ^ (forcedZeroSet f i).card) ∧
        selectedProbability f i ≤
          (1 : ℝ) / (2 ^ tournamentOutdegree T i))

def transitiveTournament {n : ℕ} (T : Fin n → Fin n → Bool) : Prop :=
  ∃ order : Fin n → Fin n,
    Function.Bijective order ∧
    ∀ ⦃a b : Fin n⦄, a.val < b.val → T (order a) (order b) = true

def claim36914_tournamentScoreMajorizationAndSharpGeometricSum
    (n : ℕ) (T : Fin n → Fin n → Bool) : Prop :=
  isTournament T →
    (∃ sorted : List ℕ,
      sorted.Perm (List.ofFn (tournamentOutdegree T)) ∧
      sorted.Pairwise (· ≤ ·) ∧
      (∀ k : ℕ, k ≤ n →
        (List.range k).sum = Nat.choose k 2 ∧
        Nat.choose k 2 ≤ (sorted.take k).sum)) ∧
    ((∑ i : Fin n,
        (1 : ℝ) / (2 ^ tournamentOutdegree T i)) ≤
      ∑ k ∈ Finset.range n, (1 : ℝ) / (2 ^ k)) ∧
    (((∑ i : Fin n,
        (1 : ℝ) / (2 ^ tournamentOutdegree T i)) =
      ∑ k ∈ Finset.range n, (1 : ℝ) / (2 ^ k)) ↔
      transitiveTournament T)

def claim36917_directionwiseUnateness
    (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool) : Prop :=
  directionwiseUnate f

end MathlibPlus.Open.Research.FormalizationBatch
