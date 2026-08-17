import MathlibPlus.Open.Analysis.AdaptiveTranscriptWalshKernel

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaSharpSpectral61144

noncomputable section

open MeasureTheory
open MathlibPlus.Open.Analysis
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable

/-- A finite or countable mixture of legal Boolean coordinate trees. -/
def admissibleTreeMixture
    {I Θ : Type*} [Countable I] [Countable Θ] [MeasurableSpace Θ]
    (M : Measure Θ) (T : Θ → AdaptiveRevealTree I) (k : ℕ) : Prop :=
  M Set.univ ≤ 1 ∧
    (∀ θ, legalAdaptiveTree (T θ) ∧ adaptiveTreeDepth (T θ) ≤ k) ∧
    (∀ x : I → ℝ,
      AEStronglyMeasurable (fun θ => adaptiveTreeRun (T θ) x) M)

/-- The fixed target mean, including the arbitrary constant term. -/
def mixtureMean
    {I Θ : Type*} [Countable I] [Countable Θ] [MeasurableSpace Θ]
    (c : ℝ) (M : Measure Θ) (T : Θ → AdaptiveRevealTree I)
    (x : I → ℝ) : ℝ :=
  c + ∫ θ, adaptiveTreeRun (T θ) x ∂M

/-- Walsh coefficients of the fixed target under the independent fair-sign law. -/
def walshCoefficient
    {I : Type*} [Countable I] (P : Measure (I → ℝ))
    (μ : (I → ℝ) → ℝ) (S : Finset I) : ℝ :=
  ∫ x, μ x * adaptiveWalshCharacter S x ∂P

def nonconstantWalshMass
    {I : Type*} [Countable I] (P : Measure (I → ℝ))
    (μ : (I → ℝ) → ℝ) : ℝ :=
  ∑' S : Finset I,
    if S.Nonempty then |walshCoefficient P μ S| else 0

/-- A nonincreasing enumeration of exactly the nonzero nonconstant Walsh
supports.  `none` is terminal, so finite support lists are included. -/
def rankedWalshBlocks
    {I : Type*} [Countable I]
    (coeff : Finset I → ℝ) (blocks : ℕ → Option (Finset I)) : Prop :=
  (∀ n S, blocks n = some S → S.Nonempty ∧ coeff S ≠ 0) ∧
    (∀ S, S.Nonempty → coeff S ≠ 0 →
      ∃ n, blocks n = some S) ∧
    (∀ n m S, n < m → blocks n = some S → blocks m ≠ some S) ∧
    (∀ n, blocks n = none → ∀ m, n ≤ m → blocks m = none) ∧
    (∀ n m S U, n < m → blocks n = some S → blocks m = some U →
      |coeff U| ≤ |coeff S|)

/-- The revealed-coordinate set after `m` entries of an answer-independent
query order. -/
def revealedCoordinates {I : Type*} [DecidableEq I]
    (q : ℕ → Option I) : ℕ → Finset I
  | 0 => ∅
  | m + 1 =>
      match q m with
      | none => revealedCoordinates q m
      | some i => insert i (revealedCoordinates q m)

def legalObliviousOrder
    {I : Type*} [DecidableEq I]
    (q : ℕ → Option I) : Prop :=
  (∀ m i, q m = some i → i ∉ revealedCoordinates q m) ∧
    (∀ m n, q m = none → q (m + n) = none)

/-- Processing blocks in order: a query belongs to a listed support, and all
earlier supports have been completed before it is queried. -/
def realizesRankedBlocks
    {I : Type*} [Countable I]
    (blocks : ℕ → Option (Finset I)) (q : ℕ → Option I) : Prop :=
  legalObliviousOrder q ∧
    (∀ n S, blocks n = some S →
      ∀ i ∈ S, ∃ m, q m = some i) ∧
    (∀ m i, q m = some i →
      ∃ n S, blocks n = some S ∧ i ∈ S ∧
        ∀ j, j < n → ∀ U, blocks j = some U →
          U ⊆ revealedCoordinates q m) 

/-- A cylinder transcript for an answer-independent coordinate order. -/
def coordinateCylinder
    {I : Type*} [DecidableEq I]
    (R : Finset I) (x : I → ℝ) : Set (I → ℝ) :=
  {y | ∀ i ∈ R, y i = x i}

def obliviousPolicyArea
    {I : Type*} [Countable I] (P : Measure (I → ℝ))
    (μ : (I → ℝ) → ℝ) (q : ℕ → Option I) : ℝ≥0∞ :=
  ∑' m : ℕ,
    ENNReal.ofReal
      (∫ x,
        adaptiveConditionalVariance P μ
          (coordinateCylinder (revealedCoordinates q m) x) ∂P)

def rankedWalshPolicy
    {I : Type*} [Countable I] (P : Measure (I → ℝ))
    (μ : (I → ℝ) → ℝ) (q : ℕ → Option I) : Prop :=
  ∃ blocks : ℕ → Option (Finset I),
    rankedWalshBlocks
      (fun S => walshCoefficient P μ S) blocks ∧
      realizesRankedBlocks blocks q

/-- Walsh spectral `ell¹` norm of one tree under the fair product law. -/
def treeWalshL1
    {I : Type*} [Countable I] (P : Measure (I → ℝ))
    (tree : AdaptiveRevealTree I) : ℝ :=
  ∑' S : Finset I,
    |∫ x, adaptiveTreeRun tree x * adaptiveWalshCharacter S x ∂P|

/-- Structural balancedness: every leaf of a legal tree occurs at the common
exact depth.  Under fair independent signs this is the balanced address-tree
condition. -/
def balancedDepthExact
    {I : Type*} (tree : AdaptiveRevealTree I) (k : ℕ) : Prop :=
  legalAdaptiveTree tree ∧ adaptiveTreeDepth tree = k ∧
    (∀ path ∈ adaptiveTreeNodes tree, ∀ output,
      adaptiveTreeAt tree path = some (.leaf output) → path.length = k)

/-- A randomized answer-oblivious order has a private seed independent of the
oracle; its area is the seed integral of the fixed-order areas. -/
def randomizedObliviousArea
    {I Θ : Type*} [Countable I] [MeasurableSpace Θ]
    (R : Measure Θ) (P : Measure (I → ℝ)) (μ : (I → ℝ) → ℝ)
    (Q : Θ → ℕ → Option I) : ℝ≥0∞ :=
  ∫⁻ θ, obliviousPolicyArea P μ (Q θ) ∂ R

def randomizedLegalObliviousOrder
    {I Θ : Type*} [DecidableEq I] [MeasurableSpace Θ]
    (R : Measure Θ) (Q : Θ → ℕ → Option I) : Prop :=
  R Set.univ = 1 ∧
    ∀ᵐ θ ∂ R, legalObliviousOrder (Q θ)

/-- Claim 61144: the exact support-independent ranked-Walsh transfer, the
sharp tree spectral norm, and the answer-oblivious exponential barrier with
its answer-adaptive linear comparison. -/
def claim_61144 : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    ∀ {I Θ : Type*} [Countable I] [Countable Θ] [MeasurableSpace Θ]
      (P : Measure (I → ℝ)) (c : ℝ) (M : Measure Θ)
      (T : Θ → AdaptiveRevealTree I),
      fairIndependentRademacher P →
      admissibleTreeMixture M T k →
      let μ := mixtureMean c M T
      ∃ q : ℕ → Option I,
        rankedWalshPolicy P μ q ∧
          obliviousPolicyArea P μ q ≤
            ENNReal.ofReal ((k : ℝ) * (4 : ℝ) ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k →
    (∀ {I : Type*} [Countable I] (P : Measure (I → ℝ))
      (tree : AdaptiveRevealTree I),
      fairIndependentRademacher P →
      legalAdaptiveTree tree →
      adaptiveTreeDepth tree ≤ k →
      treeWalshL1 P tree ≤ (2 : ℝ) ^ (k - 1)) ∧
    ∃ P : Measure (ℕ → ℝ), ∃ tree : AdaptiveRevealTree ℕ,
      fairIndependentRademacher P ∧
        balancedDepthExact tree k ∧
        treeWalshL1 P tree = (2 : ℝ) ^ (k - 1)) ∧
  (∀ k : ℕ, 1 ≤ k →
    ∃ (P : Measure (ℕ → ℝ)) (tree : AdaptiveRevealTree ℕ)
      (μ : (ℕ → ℝ) → ℝ),
      fairIndependentRademacher P ∧
        balancedDepthExact tree k ∧
        (∀ x, μ x = adaptiveTreeRun tree x) ∧
        treeWalshL1 P tree = (2 : ℝ) ^ (k - 1) ∧
        (∀ q : ℕ → Option ℕ,
          legalObliviousOrder q →
            obliviousPolicyArea P μ q ≥
              ENNReal.ofReal (((2 : ℝ) ^ (k - 1) + 1) / 2)) ∧
        (∀ {Θ : Type*} [MeasurableSpace Θ]
          (R : Measure Θ) (Q : Θ → ℕ → Option ℕ),
          randomizedLegalObliviousOrder R Q →
            randomizedObliviousArea R P μ Q ≥
              ENNReal.ofReal (((2 : ℝ) ^ (k - 1) + 1) / 2)) ∧
        adaptiveExpectedTranscriptReward P tree μ = (k : ℝ))

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaSharpSpectral61144
