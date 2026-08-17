import MathlibPlus.Open.Probability.ActiveRootMassCharging

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61125

noncomputable section

open MeasureTheory
open MathlibPlus.Open.Probability.ActiveRootMassCharging

abbrev OptionPolicy (I : Type*) :=
  RevealTranscript I → Option I

/-- The two component weights and their fixed target. -/
def twoWeights (a b : ℝ) : Fin 2 → ℝ :=
  ![a, b]

def twoTarget {I Ω : Type*}
    (a b : ℝ) (trees : Fin 2 → SignTree I) (O : I → Ω → Bool) : Ω → ℝ :=
  targetValue 2 (twoWeights a b) trees O

def componentVariance {I Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (tree : SignTree I) (O : I → Ω → Bool) : ℝ :=
  conditionalVariance P (componentValue O tree) Set.univ

/-- Execute the first supplied tree to a leaf, then the second, reusing all
 coordinates already recorded in the transcript. -/
def twoPhaseNext {I Ω : Type*}
    (first second : SignTree I) (O : I → Ω → Bool)
    (h : RevealTranscript I) : Option I :=
  letI := Classical.propDecidable
  if ¬ constantOnCell (componentValue O first) (transcriptCell O h) then
    SignTree.freshRoot first h
  else if ¬ constantOnCell (componentValue O second) (transcriptCell O h) then
    SignTree.freshRoot second h
  else
    none

/-- The scheduler chooses the first component by weighted root standard
 deviation, breaking equality in favour of the first component. -/
def weightedTwoPhasePolicy {I Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (a b : ℝ) (trees : Fin 2 → SignTree I)
    (O : I → Ω → Bool) : OptionPolicy I :=
  if a * Real.sqrt (componentVariance P (trees 0) O) ≥
      b * Real.sqrt (componentVariance P (trees 1) O) then
    twoPhaseNext (trees 0) (trees 1) O
  else
    twoPhaseNext (trees 1) (trees 0) O

/-- Reveal one fresh coordinate when the policy requests one, and otherwise
 keep the transcript fixed. -/
def optionPolicyStep {I Ω : Type*}
    (O : I → Ω → Bool) (policy : OptionPolicy I)
    (h : RevealTranscript I) (ω : Ω) : RevealTranscript I :=
  match policy h with
  | none => h
  | some i => h.update i (encodeSign (O i ω))

def optionPolicyTranscript {I Ω : Type*}
    (O : I → Ω → Bool) (policy : OptionPolicy I) :
    ℕ → Ω → RevealTranscript I
  | 0, _ => 0
  | m + 1, ω =>
      optionPolicyStep O policy
        (optionPolicyTranscript O policy m ω) ω

/-- Fresh-coordinate legality for the option-valued policy interface. -/
def optionPolicyLegal {I : Type*} (policy : OptionPolicy I) : Prop :=
  ∀ h i, policy h = some i → h i = 0

/-- Exact terminal measurability of the fixed target. -/
def optionPolicyDetermines {I Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (P : Measure Ω) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (policy : OptionPolicy I) : Prop :=
  ∀ ω, ∃ m,
    constantOnCell (targetValue n p trees O)
      (transcriptCell O (optionPolicyTranscript O policy m ω))

/-- Root-inclusive posterior-variance area, with zero tail after the target
 becomes measurable. -/
def optionPolicyArea {I Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (P : Measure Ω) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (policy : OptionPolicy I) : ℝ :=
  ∑' m : ℕ, ∫ ω,
    posteriorVariance P (targetValue n p trees O)
      (transcriptCell O (optionPolicyTranscript O policy m ω)) ∂P

/-- The parity tree on all coordinates of a finite Rademacher cube. -/
def toggleTree {I : Type*} : SignTree I → SignTree I
  | .leaf b => .leaf (Bool.not b)
  | .query i left right =>
      .query i (toggleTree left) (toggleTree right)

def liftFinTree {k : ℕ} : SignTree (Fin k) → SignTree (Fin (k + 1))
  | .leaf b => .leaf b
  | .query i left right =>
      .query i.succ (liftFinTree left) (liftFinTree right)

def parityTree : (k : ℕ) → SignTree (Fin k)
  | 0 => .leaf true
  | k + 1 =>
      let t := liftFinTree (parityTree k)
      .query 0 (toggleTree t) t

def parityPolicy (k : ℕ) : OptionPolicy (Fin k) :=
  SignTree.freshRoot (parityTree k)

/-- Sharpness of the coefficient on the fixed-level parity family. -/
def paritySharpness {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (k : ℕ) (O : Fin k → Ω → Bool) : Prop :=
  independentUniformSigns P O →
    ∀ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 →
      let trees : Fin 2 → SignTree (Fin k) := fun _ => parityTree k
      let p := twoWeights a b
      (∀ policy : OptionPolicy (Fin k),
        optionPolicyLegal policy →
          optionPolicyDetermines P p trees O policy →
            (k : ℝ) ≤ optionPolicyArea P p trees O policy) ∧
        optionPolicyLegal (parityPolicy k) ∧
          optionPolicyDetermines P p trees O (parityPolicy k) ∧
            optionPolicyArea P p trees O (parityPolicy k) = k

/-- Claim 61125: the exact weighted two-component scheduler bound for an
 arbitrary finite or countable independent Rademacher coordinate set, together
 with the positive-weight parity sharpness witness. -/
def claim61125 : Prop :=
  (∀ {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (O : I → Ω → Bool) (k : ℕ) (a b : ℝ)
    (trees : Fin 2 → SignTree I),
    independentUniformSigns P O →
    0 ≤ a ∧ 0 ≤ b ∧ a + b ≤ 1 →
    treesHaveDepthAtMost k trees →
    let policy := weightedTwoPhasePolicy P a b trees O
    optionPolicyLegal policy ∧
      optionPolicyDetermines P (twoWeights a b) trees O policy ∧
        optionPolicyArea P (twoWeights a b) trees O policy ≤
          (k : ℝ) * (a + b) ^ 2 ∧
          (k : ℝ) * (a + b) ^ 2 ≤ k) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (k : ℕ) (O : Fin k → Ω → Bool),
    paritySharpness P k O)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61125
