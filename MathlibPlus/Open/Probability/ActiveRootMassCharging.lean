import Mathlib

namespace MathlibPlus.Open.Probability.ActiveRootMassCharging

noncomputable section

open MeasureTheory
open Classical
open scoped BigOperators ENNReal

/-- A finite coordinate decision tree with sign-valued Boolean leaves. -/
inductive SignTree (I : Type*) where
  | leaf : Bool → SignTree I
  | query : I → SignTree I → SignTree I → SignTree I

namespace SignTree

def signValue (b : Bool) : ℝ := if b then 1 else -1

def evaluate : SignTree I → (I → Bool) → Bool
  | .leaf b, _ => b
  | .query i left right, oracle =>
      if oracle i then evaluate right oracle else evaluate left oracle

def depth : SignTree I → ℕ
  | .leaf _ => 0
  | .query _ left right => 1 + max left.depth right.depth

/-- Follow known transcript coordinates to the first fresh query. -/
def freshRootFuel : ℕ → SignTree I → (I →₀ Fin 3) → Option I
  | 0, _, _ => none
  | fuel + 1, .leaf _, _ => none
  | fuel + 1, .query i left right, h =>
      if h i = 0 then some i
      else freshRootFuel fuel (if h i = 2 then right else left) h

/-- The fuel is the supplied tree depth plus one. -/
def freshRoot (tree : SignTree I) (h : I →₀ Fin 3) : Option I :=
  freshRootFuel (tree.depth + 1) tree h

end SignTree

/-- Zero denotes an unrevealed coordinate; one and two encode the two signs. -/
def encodeSign (b : Bool) : Fin 3 := if b then 2 else 1

abbrev RevealTranscript (I : Type*) := I →₀ Fin 3

/-- The sample-space cell compatible with a finite reveal transcript. -/
def transcriptCell {I Ω : Type*} (O : I → Ω → Bool)
    (h : RevealTranscript I) : Set Ω :=
  {ω | ∀ i, h i ≠ 0 → h i = encodeSign (O i ω)}

def constantOnCell {Ω : Type*} (f : Ω → ℝ) (C : Set Ω) : Prop :=
  ∀ ⦃ω ω' : Ω⦄, ω ∈ C → ω' ∈ C → f ω = f ω'

def componentValue {I Ω : Type*} (O : I → Ω → Bool)
    (tree : SignTree I) : Ω → ℝ :=
  fun ω => SignTree.signValue (tree.evaluate (fun i => O i ω))

def targetValue {I Ω : Type*} (n : ℕ) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool) : Ω → ℝ :=
  fun ω => ∑ j : Fin n, p j * componentValue O (trees j) ω

def markedComponent {I Ω : Type*} (n : ℕ) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (h : RevealTranscript I) (j : Fin n) : Prop :=
  0 < p j ∧
    constantOnCell (componentValue O (trees j)) (transcriptCell O h)

def groupMembers {I Ω : Type*} (n : ℕ) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (h : RevealTranscript I) (i : I) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j =>
    ¬ markedComponent n p trees O h j ∧
      SignTree.freshRoot (trees j) h = some i)

def activeMass {I Ω : Type*} (n : ℕ) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (h : RevealTranscript I) (i : I) : ℝ :=
  ∑ j ∈ groupMembers n p trees O h i, p j

def groupedComponent {I Ω : Type*} (n : ℕ) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (h : RevealTranscript I) (i : I) : Ω → ℝ :=
  fun ω => ∑ j ∈ groupMembers n p trees O h i,
    p j * componentValue O (trees j) ω

/-- The finite set of active fresh roots of the supplied finite family. -/
noncomputable def activeRoots {I Ω : Type*} (n : ℕ) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (h : RevealTranscript I) : Finset I := by
  classical
  exact (Finset.univ : Finset (Fin n)).biUnion (fun j =>
    if markedComponent n p trees O h j then ∅
    else (SignTree.freshRoot (trees j) h).toFinset)

/-- Conditional expectation on a measurable transcript cell. -/
def conditionalMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else (∫ ω in C, f ω ∂P) / (P C).toReal

def conditionalVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else
    (∫ ω in C, (f ω - conditionalMean P f C) ^ 2 ∂P) / (P C).toReal

/-- Variance is explicitly zero on a cell on which the target is measurable. -/
noncomputable def posteriorVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ := by
  classical
  exact if constantOnCell f C then 0 else conditionalVariance P f C

def conditionalCovariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → ℝ) (C : Set Ω) : ℝ :=
  conditionalMean P (fun ω => f ω * g ω) C -
    conditionalMean P f C * conditionalMean P g C

/-- Cylinder measurability and the exact one-half law for every finite transcript. -/
def independentUniformSigns {I Ω : Type*} [Countable I]
    [MeasurableSpace Ω] (P : Measure Ω) (O : I → Ω → Bool) : Prop :=
  (∀ i, Measurable (fun ω => O i ω)) ∧
    (∀ h : RevealTranscript I,
      MeasurableSet (transcriptCell O h) ∧
        P (transcriptCell O h) = ((1 : ENNReal) / 2) ^
          (Finsupp.support h).card) ∧
    (∀ (n : ℕ) (t : SignTree I),
      Measurable (fun ω => componentValue O t ω))

def validMixtureWeights {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j : Fin n, p j = 1

def treesHaveDepthAtMost {I : Type*} {n : ℕ} (k : ℕ)
    (trees : Fin n → SignTree I) : Prop :=
  ∀ j, (trees j).depth ≤ k

/-- The deterministic policy chooses a fresh root of maximum active mass. -/
def legalMaximizingPolicy {I Ω : Type*} {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignTree I)
    (O : I → Ω → Bool) (policy : RevealTranscript I → I) : Prop :=
  ∀ h, ¬ constantOnCell (targetValue n p trees O) (transcriptCell O h) →
    policy h ∉ Finsupp.support h ∧
      policy h ∈ activeRoots n p trees O h ∧
        ∀ i, activeMass n p trees O h i ≤
          activeMass n p trees O h (policy h)

noncomputable def policyStep {I Ω : Type*} {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (policy : RevealTranscript I → I) (h : RevealTranscript I) (ω : Ω) :
    RevealTranscript I := by
  classical
  exact if constantOnCell (targetValue n p trees O) (transcriptCell O h) then h
    else h.update (policy h) (encodeSign (O (policy h) ω))

noncomputable def policyTranscript {I Ω : Type*} {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (policy : RevealTranscript I → I) : ℕ → Ω → RevealTranscript I
  | 0, _ => 0
  | m + 1, ω =>
      policyStep p trees O policy (policyTranscript p trees O policy m ω) ω

def reachedTranscript {I Ω : Type*} {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (policy : RevealTranscript I → I) (h : RevealTranscript I) : Prop :=
  ∃ m ω, policyTranscript p trees O policy m ω = h

def determinesTarget {I Ω : Type*} {n : ℕ}
    (p : Fin n → ℝ) (trees : Fin n → SignTree I) (O : I → Ω → Bool)
    (policy : RevealTranscript I → I) : Prop :=
  ∀ ω, ∃ m,
    constantOnCell (targetValue n p trees O)
      (transcriptCell O (policyTranscript p trees O policy m ω))

def posteriorVarianceArea {I Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (p : Fin n → ℝ) (trees : Fin n → SignTree I)
    (O : I → Ω → Bool) (policy : RevealTranscript I → I) : ℝ :=
  ∑' m : ℕ, ∫ ω,
    posteriorVariance P (targetValue n p trees O)
      (transcriptCell O (policyTranscript p trees O policy m ω)) ∂P

/-- The unordered finite-pair form of the displayed `i < ell` covariance sum. -/
def groupedCovarianceSum {I Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (p : Fin n → ℝ) (trees : Fin n → SignTree I)
    (O : I → Ω → Bool) (h : RevealTranscript I) : ℝ := by
  classical
  exact (1 / 2 : ℝ) *
    ∑ i ∈ activeRoots n p trees O h,
      ∑ ell ∈ (activeRoots n p trees O h).filter (fun ell => ell ≠ i),
        conditionalCovariance P
          (groupedComponent n p trees O h i)
          (groupedComponent n p trees O h ell)
          (transcriptCell O h)

def activeMassCertificate {I Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (p : Fin n → ℝ) (trees : Fin n → SignTree I)
    (O : I → Ω → Bool) (policy : RevealTranscript I → I) : Prop :=
  ∀ h, reachedTranscript p trees O policy h →
    ¬ constantOnCell (targetValue n p trees O) (transcriptCell O h) →
      posteriorVariance P (targetValue n p trees O) (transcriptCell O h) ≤
        activeMass n p trees O h (policy h)

def groupedCovarianceCertificate {I Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (p : Fin n → ℝ) (trees : Fin n → SignTree I)
    (O : I → Ω → Bool) (policy : RevealTranscript I → I) : Prop :=
  ∀ h, reachedTranscript p trees O policy h →
    ¬ constantOnCell (targetValue n p trees O) (transcriptCell O h) →
      groupedCovarianceSum P p trees O h ≤ 0

/-- Formal statement of the finite-mixture active-root theorem. -/
def activeRootMassChargingTheorem : Prop :=
  ∀ {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (O : I → Ω → Bool) (p : Fin n → ℝ)
    (trees : Fin n → SignTree I)
    (policy : RevealTranscript I → I),
    independentUniformSigns P O →
    validMixtureWeights p →
    treesHaveDepthAtMost k trees →
    legalMaximizingPolicy p trees O policy →
    (activeMassCertificate P p trees O policy →
      determinesTarget p trees O policy ∧
        posteriorVarianceArea P p trees O policy ≤ (k : ℝ)) ∧
    (∀ h, ¬ constantOnCell (targetValue n p trees O) (transcriptCell O h) →
      groupedCovarianceSum P p trees O h ≤ 0 →
      posteriorVariance P (targetValue n p trees O)
        (transcriptCell O h) ≤ activeMass n p trees O h (policy h)) ∧
    (groupedCovarianceCertificate P p trees O policy →
      activeMassCertificate P p trees O policy)

end
end MathlibPlus.Open.Probability.ActiveRootMassCharging
