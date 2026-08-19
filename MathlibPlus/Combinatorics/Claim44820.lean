import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0014f_9da0_7b3c_8e09_26f26436e566

open scoped BigOperators
open BigOperators
open Classical

namespace MathlibPlus.Combinatorics.Claim44820

noncomputable section

abbrev SelectorCoordinate44820 (n : ℕ) := Sum (Fin n) (Fin 2)
abbrev SelectorInput44820 (n : ℕ) := SelectorCoordinate44820 n → Bool
abbrev SelectorOutcome44820 (n : ℕ) := (Fin 2 → Bool) × (Fin n → Bool)
abbrev SelectorTranscript44820 (n m : ℕ) :=
  {h : (Fin m → Fin n) × (Fin m → Bool) // Function.Injective h.1}
abbrev SharedSelectorTree44820 (n : ℕ) :=
  MathlibPlus.Open.ResearchFormalizationBatch.DecisionTree
    (SelectorCoordinate44820 n)

def signValue44820 (b : Bool) : ℚ := if b then 1 else -1

def sharedSelectorTree44820 (n : ℕ) (i : Fin n) : SharedSelectorTree44820 n :=
  .query (Sum.inl i)
    (.query (Sum.inr 0) (.leaf false) (.leaf true))
    (.query (Sum.inr 1) (.leaf false) (.leaf true))

def treeDepth44820 : SharedSelectorTree44820 n → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (treeDepth44820 negative) (treeDepth44820 positive)

def expectedComponentDepth44820
    (n : ℕ) (i : Fin n) : ℚ :=
  (∑ ω : SelectorInput44820 n,
      (MathlibPlus.Open.ResearchFormalizationBatch.DecisionTree.queryCount
        (sharedSelectorTree44820 n i) ω : ℚ)) /
    (Fintype.card (SelectorInput44820 n) : ℚ)

def sharedSelectorValue44820
    {n : ℕ} (i : Fin n) (ω : SelectorOutcome44820 n) : ℚ :=
  if ω.2 i then signValue44820 (ω.1 1) else signValue44820 (ω.1 0)

def sharedSelectorMean44820
    (n : ℕ) (ω : SelectorOutcome44820 n) : ℚ :=
  (∑ i : Fin n, sharedSelectorValue44820 i ω) / (n : ℚ)

def selectorAgrees44820
    {n m : ℕ} (h : SelectorTranscript44820 n m)
    (ω : SelectorOutcome44820 n) : Prop :=
  ∀ j : Fin m, ω.2 (h.1.1 j) = h.1.2 j

noncomputable def selectorConditionalMean44820
    {n m : ℕ} (h : SelectorTranscript44820 n m) : ℚ :=
  let denominator : ℚ :=
    ∑ ω : SelectorOutcome44820 n,
      if selectorAgrees44820 h ω then 1 else 0
  (∑ ω : SelectorOutcome44820 n,
      if selectorAgrees44820 h ω then sharedSelectorMean44820 n ω else 0) /
    denominator

noncomputable def selectorConditionalVariance44820
    {n m : ℕ} (h : SelectorTranscript44820 n m) : ℚ :=
  let μ := selectorConditionalMean44820 h
  let denominator : ℚ :=
    ∑ ω : SelectorOutcome44820 n,
      if selectorAgrees44820 h ω then 1 else 0
  (∑ ω : SelectorOutcome44820 n,
      if selectorAgrees44820 h ω then
        (sharedSelectorMean44820 n ω - μ) ^ 2 else 0) /
    denominator

def tailProbability44820 (n m : ℕ) : ℚ :=
  (Fintype.card {f : Fin m → Fin n // Function.Injective f} : ℚ) /
    (n : ℚ) ^ m

def expectedFirstRepeat44820 (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + 1), tailProbability44820 n m

def halfTailSum44820 (n : ℕ) : ℚ :=
  (1 / 2 : ℚ) * expectedFirstRepeat44820 n

/-- The exact expected charge accumulated on selector-only transcripts before
any repeated component selection. -/
noncomputable def selectorOnlyStage44820 (n m : ℕ) : ℚ :=
  (∑ h : SelectorTranscript44820 n m,
      selectorConditionalVariance44820 h) /
    ((n : ℚ) ^ m * (2 : ℚ) ^ m)

noncomputable def selectorOnlyPosteriorArea44820 (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range (n + 1), selectorOnlyStage44820 n m

def IsSqrtOmega44820 (a : ℕ → ℚ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    c * Real.sqrt n ≤ (a n : ℝ)

/-- The exact finite uniform-selector tail probability. -/
def sharedSelector_tailProbability_claim44820 (n m : ℕ) : Prop :=
  tailProbability44820 n m =
    (Nat.descFactorial n m : ℚ) / (n : ℚ) ^ m

/-- The exact first-repeat expectation as the sum of the tail probabilities. -/
def sharedSelector_expectedTail_claim44820 (n : ℕ) : Prop :=
  expectedFirstRepeat44820 n =
    ∑ m ∈ Finset.range (n + 1),
      (Nat.descFactorial n m : ℚ) / (n : ℚ) ^ m

/-- The retained exact half-tail value at `n=5`. -/
def sharedSelector_halfTailSum_n5_claim44820 : Prop :=
  halfTailSum44820 5 = 2194 / 1250

/-- Claim 44820's shared-selector obstruction.  The selector-only posterior
variance and its square-root lower bound are explicit.  The receipt alignment
records that the post-repeat continuation of the full resampling policy is not
reconstructed by this carrier. -/
def sharedSelector_posteriorVarianceObstruction_claim44820 : Prop :=
  (∀ n : ℕ, ∀ i : Fin n,
    treeDepth44820 (sharedSelectorTree44820 n i) = 2 ∧
      expectedComponentDepth44820 n i = 2) ∧
  (∀ n : ℕ, 1 ≤ n →
    ∀ m : ℕ, m ≤ n →
      ∀ h : SelectorTranscript44820 n m,
        (1 / 2 : ℚ) ≤ selectorConditionalVariance44820 h) ∧
  (∀ n : ℕ, 1 ≤ n →
    halfTailSum44820 n ≤ selectorOnlyPosteriorArea44820 n) ∧
  IsSqrtOmega44820 halfTailSum44820 ∧
  sharedSelector_halfTailSum_n5_claim44820

end

end MathlibPlus.Combinatorics.Claim44820
