import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.Combinatorics.AdmittedThreeSunflower

/-- A finite indexed set family, with the index set kept explicit so that
incidence degrees count members rather than only distinct traces. -/
def UniformDistinct {ι α : Type*} [DecidableEq α]
    (F : ι → Finset α) (n : ℕ) : Prop :=
  (∀ i, (F i).card = n) ∧ Function.Injective F

def support {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : ι → Finset α) (x : α) : Finset ι :=
  Finset.univ.filter (fun i => x ∈ F i)

def degree {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : ι → Finset α) (x : α) : ℕ :=
  (support F x).card

def incidenceSum {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (F : ι → Finset α) : ℕ :=
  ∑ x : α, (support F x).card

def kSunflowerFree {ι α : Type*} [DecidableEq α]
    (k : ℕ) (F : ι → Finset α) : Prop :=
  ∀ I : Finset ι, I.card = k →
    ¬ ∃ C : Finset α,
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → F i ∩ F j = C

def threeSunflowerFree {ι α : Type*} [DecidableEq α]
    (F : ι → Finset α) : Prop :=
  kSunflowerFree 3 F

def traceFamily {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : ι → Finset α) (H : Finset α) : Finset (Finset α) :=
  Finset.univ.image (fun i => F i ∩ H)

def traceClass {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : ι → Finset α) (H t : Finset α) : Finset ι :=
  Finset.univ.filter (fun i => F i ∩ H = t)

def heavyCoordinates {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (F : ι → Finset α) (D : ℕ) : Finset α :=
  Finset.univ.filter (fun x => D < degree F x)

def residualDegree {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : ι → Finset α) (C : Finset ι) (x : α) : ℕ :=
  (C.filter (fun i => x ∈ F i)).card

def pairwiseDisjointIndices {ι α : Type*} [DecidableEq α]
    (F : ι → Finset α) (I : Finset ι) : Prop :=
  ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j → Disjoint (F i) (F j)

def missingPatterns {ι α : Type*} [Fintype ι] [DecidableEq α]
    (F : ι → Finset α) (H : Finset α) : Finset (Finset α) :=
  Finset.univ.image (fun i => H \ F i)

/-- The integral incidence identity and the logarithmic lower-bound target are
kept in one statement; no fractional relaxation is substituted for the
integral support data. -/
def integralSupportLowerBound_claim34615 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (α : Type*) [Fintype α] [DecidableEq α] (m n : ℕ)
      (F : Fin m → Finset α),
      m₀ ≤ m → UniformDistinct F n → threeSunflowerFree F →
      incidenceSum F = m * n ∧
        (n : ℝ) ≥ c * Real.log (m : ℝ)

/-- Exact integral signature collision count, followed by the two stated
quadratic consequences. -/
def signatureCollisionInequality_claim34617 : Prop :=
  ∀ (α : Type*) [Fintype α] [DecidableEq α] (m n : ℕ)
    (F : Fin m → Finset α) (H : Finset α),
    0 < m → UniformDistinct F n → threeSunflowerFree F →
    let T := traceFamily F H
    let q := T.card
    let Q := (∑ x ∈ (Finset.univ \ H), degree F x * (degree F x - 1))
    (∑ t ∈ T, ((traceClass F H t).card).choose 3) ≤
        (∑ x ∈ (Finset.univ \ H),
          (degree F x).choose 2 * (m - degree F x)) ∧
    (max 0 ((m : ℝ) - 2 * (q : ℝ))) ^ 3 /
          (6 * (q : ℝ) ^ 2) ≤
        (∑ x ∈ (Finset.univ \ H),
          ((((degree F x).choose 2 * (m - degree F x) : ℕ) : ℝ))) ∧
    (m : ℝ) ≤ 4 * (q : ℝ) + Real.sqrt 24 * (q : ℝ) * Real.sqrt (Q : ℝ)

/-- The bounded-heavy-coordinate theorem with the natural finite incidence
model made explicit. -/
def boundedHeavyCoordinateTheorem_claim34618 : Prop :=
  ∀ (k D : ℕ) (β : ℝ),
    3 ≤ k → 1 ≤ D → 0 ≤ β →
    ∀ (α : Type*) [Fintype α] [DecidableEq α] (m n : ℕ)
      (F : Fin m → Finset α),
      UniformDistinct F n → kSunflowerFree k F →
      ((heavyCoordinates F D).card : ℝ) ≤ β * (n : ℝ) →
      (m : ℝ) ≤ (((k - 1) * D * n : ℕ) : ℝ) *
        Real.rpow 2 (β * (n : ℝ))

/-- A maximal disjoint subfamily, its covering property, and the incidence
bound are all recorded rather than only the final numerical inequality. -/
def boundedDegreeClassLemma_claim34619 : Prop :=
  ∀ (k D : ℕ) (m n : ℕ)
    (α : Type*) [Fintype α] [DecidableEq α]
    (F : Fin m → Finset α),
    3 ≤ k → 1 ≤ D → 1 ≤ n → UniformDistinct F n →
    kSunflowerFree k F →
    (∀ x : α, degree F x ≤ D) →
    ∃ I : Finset (Fin m),
      pairwiseDisjointIndices F I ∧ I.card ≤ k - 1 ∧
      (∀ j : Fin m, j ∉ I →
        ∃ i ∈ I, ¬ Disjoint (F i) (F j)) ∧
      (∀ j : Fin m, ∃ i ∈ I, (F i ∩ F j).Nonempty) ∧
      m ≤ (k - 1) * D * n

def sharpenedBound (D n : ℕ) : ℕ :=
  if D = 1 then 2 else min (2 * D * n) (3 * (D - 1) * n + 3)

/-- The sharpened class estimate, including both the residual witness count
and the resulting full-family bound. -/
def sharpenedThreeSunflowerTraceClass_claim34620 : Prop :=
  ∀ (D : ℕ) (β : ℝ) (m n : ℕ)
    (α : Type*) [Fintype α] [DecidableEq α]
    (F : Fin m → Finset α),
    1 ≤ D → 1 ≤ n → 0 ≤ β → UniformDistinct F n →
    threeSunflowerFree F →
    ((heavyCoordinates F D).card : ℝ) ≤ β * (n : ℝ) →
    let H := heavyCoordinates F D
    (∀ T, T ∈ traceFamily F H →
      let C := traceClass F H T
      let a := C.card
      (((a.choose 3 : ℕ) : ℝ) ≤
          (((D - 1 : ℕ) : ℝ) * (a : ℝ) / 2) *
            (∑ x ∈ (Finset.univ \ H), (residualDegree F C x : ℝ))) ∧
        (((((D - 1 : ℕ) : ℝ) * (a : ℝ) / 2) *
            (∑ x ∈ (Finset.univ \ H), (residualDegree F C x : ℝ))) ≤
          (((D - 1 : ℕ) : ℝ) * (n : ℝ) * (a : ℝ) ^ 2 / 2)) ∧
        (2 ≤ D → a ≤ 3 * (D - 1) * n + 3) ∧
        (D = 1 → a ≤ 2) ∧
        a ≤ 2 * D * n) ∧
    (m : ℝ) ≤ (sharpenedBound D n : ℝ) * Real.rpow 2 (β * (n : ℝ))

/-- Finite Shannon entropy of the pushforward of the uniform law by a map. -/
def uniformMapEntropy {ι β : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] (f : ι → β) : ℝ :=
  -∑ y : β,
    (((Finset.univ.filter (fun i => f i = y)).card : ℝ) /
      (Fintype.card ι : ℝ)) *
      Real.log (((Finset.univ.filter (fun i => f i = y)).card : ℝ) /
        (Fintype.card ι : ℝ))

def binaryEntropy (p : ℝ) : ℝ :=
  -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- The joint-trace entropy sandwich and its scalar logarithmic interface. -/
def heavyTraceEntropySandwich_claim34621 : Prop :=
  ∀ (k D m n : ℕ) (L : ℝ)
    (α : Type*) [Fintype α] [DecidableEq α]
    (F : Fin m → Finset α),
    3 ≤ k → 1 ≤ D → 1 ≤ n → 0 < m → 0 < L →
    UniformDistinct F n → kSunflowerFree k F →
    let H := heavyCoordinates F D
    let Z : Fin m → Finset α := fun i => F i ∩ H
    (∀ t, ((traceClass F H t).card : ℝ) ≤ L) →
      (Real.log ((m : ℝ) / L) ≤ uniformMapEntropy Z ∧
        uniformMapEntropy Z ≤
          (∑ x ∈ H, binaryEntropy ((degree F x : ℝ) / (m : ℝ))) ∧
        Real.log (m : ℝ) ≤ Real.log L +
          (∑ x ∈ H, binaryEntropy ((degree F x : ℝ) / (m : ℝ)))) ∧
      (k = 3 →
        (∀ t, ((traceClass F H t).card : ℝ) ≤ sharpenedBound D n) ∧
        Real.log ((m : ℝ) / (sharpenedBound D n : ℝ)) ≤
          uniformMapEntropy Z ∧
        uniformMapEntropy Z ≤
          (∑ x ∈ H, binaryEntropy ((degree F x : ℝ) / (m : ℝ))) ∧
        Real.log (m : ℝ) ≤ Real.log (sharpenedBound D n : ℝ) +
          (∑ x ∈ H, binaryEntropy ((degree F x : ℝ) / (m : ℝ))))

/-- Missing-pattern counting uses actual omissions, not a marginal alphabet
payment. -/
def omissionTraceCount_claim34623 : Prop :=
  ∀ (D E m n : ℕ)
    (α : Type*) [Fintype α] [DecidableEq α]
    (F : Fin m → Finset α),
    UniformDistinct F n →
    (∀ x : α, degree F x ≤ D ∨ m - E ≤ degree F x) →
    let H := heavyCoordinates F D
    let P := missingPatterns F H
    let q := P.card
    (P.filter (fun M => M = ∅)).card ≤ 1 ∧
      q - 1 ≤ (∑ i : Fin m, (H \ F i).card) ∧
      (∑ i : Fin m, (H \ F i).card) =
        (∑ x ∈ H, (m - degree F x)) ∧
      (m > 2 * E → H.card < 2 * n → q ≤ 2 * E * n + 1)

def finsetFamilyKSunflowerFree {α : Type*} [DecidableEq α]
    (k : ℕ) (G : Finset (Finset α)) : Prop :=
  ∀ I : Finset (Finset α), I.card = k → I ⊆ G →
    ¬ ∃ C : Finset α,
      ∀ A ∈ I, ∀ B ∈ I, A ≠ B → A ∩ B = C

def sequenceDegree (F : ℕ → Finset (Finset ℕ)) (n : ℕ) (x : ℕ) : ℕ :=
  ((F n).filter (fun A => x ∈ A)).card

/-- The quadratic two-sided degree-gap consequence for a sequence of finite
families is stated with the quantifiers that express ``faster than O(n²)''. -/
def mediumDegreeCoordinate_claim34624 : Prop :=
  ∀ (k D E : ℕ) (F : ℕ → Finset (Finset ℕ)),
    3 ≤ k → 1 ≤ D → 1 ≤ E →
    (∀ n, (∀ A ∈ F n, A.card = n) ∧
      finsetFamilyKSunflowerFree k (F n)) →
    (∀ C : ℕ, ∃ n, C * n ^ 2 < (F n).card) →
    (∀ n x, sequenceDegree F n x ≤ D ∨
      (F n).card - E ≤ sequenceDegree F n x) →
    ∃ n x, D < sequenceDegree F n x ∧
      sequenceDegree F n x < (F n).card - E

def allSSubsets (M s : ℕ) : Finset (Finset (Fin M)) :=
  Finset.univ.filter (fun S : Finset (Fin M) => S.card = s)

def balancedSupportMember (M s : ℕ) (i : Fin M) : Finset (Finset (Fin M)) :=
  (allSSubsets M s).filter (fun S => i ∈ S)

/-- The integral balanced-support construction realizes the entire
medium-degree range. -/
def balancedSupportFamily_claim34625 : Prop :=
  ∀ M s : ℕ, 2 ≤ s → s ≤ M - 1 →
    (∀ i : Fin M,
      (balancedSupportMember M s i).card = Nat.choose (M - 1) (s - 1)) ∧
    (∀ S ∈ allSSubsets M s,
      degree (balancedSupportMember M s) S = s) ∧
    Function.Injective (balancedSupportMember M s) ∧
    threeSunflowerFree (balancedSupportMember M s) ∧
    (∀ i j k : Fin M, i ≠ j → i ≠ k → j ≠ k →
      ∃ S ∈ allSSubsets M s, i ∈ S ∧ j ∈ S ∧ k ∉ S) ∧
    (∀ D E : ℕ, D < s → s < M - E →
      ∀ S ∈ allSSubsets M s,
        D < degree (balancedSupportMember M s) S ∧
          degree (balancedSupportMember M s) S < M - E)

def completeEdges (M : ℕ) : Finset (Finset (Fin M)) :=
  Finset.univ.filter (fun E : Finset (Fin M) => E.card = 2)

def edgeOf {M : ℕ} (i j : Fin M) : Finset (Fin M) :=
  insert i {j}

def completeGraphDualMember (M : ℕ) (i : Fin M) : Finset (Finset (Fin M)) :=
  (completeEdges M).filter (fun E => i ∈ E)

/-- The complete-graph dual family is recorded by its actual two-subset
coordinates and exact pair intersections. -/
def completeGraphDualFamily_claim34626 : Prop :=
  ∀ M : ℕ, 3 ≤ M →
    (∀ i : Fin M,
      (completeGraphDualMember M i).card = M - 1) ∧
    (∀ E ∈ completeEdges M,
      degree (completeGraphDualMember M) E = 2) ∧
    Function.Injective (completeGraphDualMember M) ∧
    threeSunflowerFree (completeGraphDualMember M) ∧
    (∀ i j : Fin M, i ≠ j →
      completeGraphDualMember M i ∩ completeGraphDualMember M j = {edgeOf i j}) ∧
    (∀ i j k : Fin M, i ≠ j → i ≠ k → j ≠ k →
      edgeOf i j ≠ edgeOf i k ∧ edgeOf i j ≠ edgeOf j k ∧
        edgeOf i k ≠ edgeOf j k)

/-- The complete-block entropy defect, including the marginal bounds and the
linear loss factor. -/
def completeGraphEntropyDefect_claim34627 : Prop :=
  ∀ M : ℕ, 4 ≤ M →
    let S : ℝ :=
      (∑ E ∈ completeEdges M, binaryEntropy (2 / (M : ℝ)))
    (uniformMapEntropy (completeGraphDualMember M) = Real.log (M : ℝ)) ∧
      (∀ E ∈ completeEdges M,
        (((Finset.univ : Finset (Fin M)).filter
          (fun i => E ∈ completeGraphDualMember M i)).card : ℝ) /
            (M : ℝ) = 2 / (M : ℝ)) ∧
      (M - 1 : ℝ) * Real.log (M / 2) ≤ S ∧
      S ≤ (M - 1 : ℝ) * (Real.log (M / 2) + 1) ∧
      S / Real.log (M : ℝ) ≥ (M - 1 : ℝ) / 2

def productMember {ι κ α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : ι → Finset α) (B : κ → Finset β)
    (ij : ι × κ) : Finset (Sum α β) :=
  (A ij.1).image Sum.inl ∪ (B ij.2).image Sum.inr

abbrev BlockIndex (r : ℕ) (M : Fin r → ℕ) :=
  ∀ j : Fin r, Fin (M j)

abbrev BlockCoordinate (r : ℕ) (M : Fin r → ℕ) :=
  Σ j : Fin r, {E : Finset (Fin (M j)) // E.card = 2}

def blockMember {r : ℕ} (M : Fin r → ℕ) (a : BlockIndex r M) :
    Finset (BlockCoordinate r M) :=
  Finset.univ.filter (fun e => a e.1 ∈ e.2.1)

def blockTrace {r : ℕ} (M : Fin r → ℕ) (J : Finset (Fin r))
    (a : BlockIndex r M) : Finset (BlockCoordinate r M) :=
  Finset.univ.filter (fun e => e.1 ∈ J ∧ a e.1 ∈ e.2.1)

def blockUniformity {r : ℕ} (M : Fin r → ℕ) : ℕ :=
  ∑ j : Fin r, (M j - 1)

def blockMarginal {r : ℕ} (M : Fin r → ℕ) (j : Fin r)
    (E : {E : Finset (Fin (M j)) // E.card = 2}) : ℝ :=
  ((Finset.univ.filter (fun a : BlockIndex r M =>
      Sigma.mk j E ∈ blockMember M a)).card : ℝ) /
    (Fintype.card (BlockIndex r M) : ℝ)

/-- Direct products preserve three-sunflower-freeness; the dependent block
model then states the exact product cardinality, uniformity, and entropy sums. -/
def directProductAndEntropyDefect_claim34628 : Prop :=
  (∀ {ι κ α β : Type*} [Fintype ι] [Fintype κ]
      [DecidableEq α] [DecidableEq β]
      (A : ι → Finset α) (B : κ → Finset β) (a b : ℕ),
      UniformDistinct A a → UniformDistinct B b →
      threeSunflowerFree A → threeSunflowerFree B →
      UniformDistinct (productMember A B) (a + b) ∧
        threeSunflowerFree (productMember A B)) ∧
  (∀ (r : ℕ) (M : Fin r → ℕ),
      (∀ j, 3 ≤ M j) →
      Fintype.card (BlockIndex r M) = ∏ j : Fin r, M j ∧
      (∀ a : BlockIndex r M,
        (blockMember M a).card = blockUniformity M) ∧
      Function.Injective (blockMember M) ∧
      threeSunflowerFree (blockMember M) ∧
      (∀ j (E : {E : Finset (Fin (M j)) // E.card = 2}),
        blockMarginal M j E = 2 / (M j : ℝ)) ∧
      (∀ J : Finset (Fin r),
        uniformMapEntropy (blockTrace M J) =
            (∑ j ∈ J, Real.log (M j : ℝ)) ∧
        (∑ j ∈ J,
          ∑ E : {E : Finset (Fin (M j)) // E.card = 2},
            binaryEntropy (blockMarginal M j E)) =
          (∑ j ∈ J, (Nat.choose (M j) 2 : ℝ) *
            binaryEntropy (2 / (M j : ℝ)))))

end MathlibPlus.Open.Combinatorics.AdmittedThreeSunflower
