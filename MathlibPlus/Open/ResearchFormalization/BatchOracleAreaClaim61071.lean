import Mathlib

open scoped BigOperators ENNReal

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchOracleAreaClaim61071

open MeasureTheory

attribute [local instance] Classical.decEq Classical.propDecidable

abbrev RademacherSign := Bool

private def signValue (s : RademacherSign) : ℝ :=
  if s then 1 else -1

/-- A component of depth at most one, with real-valued bounded leaves. -/
inductive DepthOneTree (I : Type*) where
  | leaf : ℝ → DepthOneTree I
  | query : I → ℝ → ℝ → DepthOneTree I

private def treeEvaluateAt {I : Type*}
    (tree : DepthOneTree I) (x : I → RademacherSign) : ℝ :=
  match tree with
  | .leaf value => value
  | .query coordinate negative positive =>
      if x coordinate then positive else negative

private def treeBounded {I : Type*} : DepthOneTree I → Prop
  | .leaf value => -1 ≤ value ∧ value ≤ 1
  | .query _ negative positive =>
      -1 ≤ negative ∧ negative ≤ 1 ∧
        -1 ≤ positive ∧ positive ≤ 1

private def treeCoordinate {I : Type*} :
    DepthOneTree I → Option I
  | .leaf _ => none
  | .query coordinate _ _ => some coordinate

private def treeSlope {I : Type*} : DepthOneTree I → ℝ
  | .leaf _ => 0
  | .query _ negative positive => (positive - negative) / 2

private def validMixture {C : Type*} [Countable C]
    (p : C → ℝ) : Prop :=
  (∀ c, 0 ≤ p c) ∧ Summable p ∧ ∑' c, p c = 1

private def independentRademacher
    {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    (P : Measure Ω) (X : I → Ω → RademacherSign) : Prop :=
  (∀ i, Measurable (X i)) ∧
    ∀ (S : Finset I) (a : I → RademacherSign),
      P {ω | ∀ i ∈ S, X i ω = a i} =
        ((1 : ENNReal) / 2) ^ S.card

private abbrev Transcript (I : Type*) := I →₀ Fin 3

private def encodeSign (s : RademacherSign) : Fin 3 :=
  if s then 2 else 1

private def transcriptCell
    {I Ω : Type*} (X : I → Ω → RademacherSign)
    (h : Transcript I) : Set Ω :=
  {ω | ∀ i, h i ≠ 0 → h i = encodeSign (X i ω)}

private def mixtureTarget
    {I C Ω : Type*} [Countable C]
    (p : C → ℝ) (trees : C → DepthOneTree I)
    (X : I → Ω → RademacherSign) : Ω → ℝ :=
  fun ω => ∑' c, p c * treeEvaluateAt (trees c) (fun i => X i ω)

private def aggregateCoefficient
    {I C : Type*} [Countable C]
    (p : C → ℝ) (trees : C → DepthOneTree I) (i : I) : ℝ :=
  ∑' c, p c *
    (if treeCoordinate (trees c) = some i then treeSlope (trees c) else 0)

private def relevantCoordinate
    {I C : Type*} [Countable C]
    (p : C → ℝ) (trees : C → DepthOneTree I) (i : I) : Prop :=
  aggregateCoefficient p trees i ≠ 0

private def scheduleWellFormed
    {I C : Type*} [Countable C]
    (p : C → ℝ) (trees : C → DepthOneTree I)
    (q : ℕ → Option I) : Prop :=
  (∀ m n i, m < n → q m = some i → q n ≠ some i) ∧
    (∀ m n, m < n → q m = none → q n = none) ∧
    (∀ n i, q n = some i → relevantCoordinate p trees i) ∧
    (∀ i, relevantCoordinate p trees i → ∃ n, q n = some i) ∧
    (∀ m n i j, m < n → q m = some i → q n = some j →
      |aggregateCoefficient p trees i| ≥
        |aggregateCoefficient p trees j|)

private def transcriptAt
    {I Ω : Type*} (X : I → Ω → RademacherSign)
    (q : ℕ → Option I) : ℕ → Ω → Transcript I
  | 0, _ => 0
  | n + 1, ω =>
      let h := transcriptAt X q n ω
      match q n with
      | none => h
      | some i => Finsupp.update h i (encodeSign (X i ω))

private def conditionalMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else
    (∫ ω in C, F ω ∂P) / (P C).toReal

private def conditionalVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else
    (∫ ω in C,
      (F ω - conditionalMean P F C) ^ 2 ∂P) / (P C).toReal

private def expectedPosteriorVariance
    {I Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : I → Ω → RademacherSign)
    (F : Ω → ℝ) (q : ℕ → Option I) (n : ℕ) : ℝ :=
  ∫ ω,
    conditionalVariance P F
      (transcriptCell X (transcriptAt X q n ω)) ∂P

private def rootInclusiveArea
    {I C Ω : Type*} [Countable C] [MeasurableSpace Ω]
    (P : Measure Ω) (X : I → Ω → RademacherSign)
    (p : C → ℝ) (trees : C → DepthOneTree I)
    (q : ℕ → Option I) : ℝ :=
  ∑' n : ℕ,
    expectedPosteriorVariance P X (mixtureTarget p trees X) q n

private def boolAverage (f : Bool → ℝ) : ℝ :=
  (f false + f true) / 2

private def boolVariance (f : Bool → ℝ) : ℝ :=
  ((f false - boolAverage f) ^ 2 +
    (f true - boolAverage f) ^ 2) / 2

private def sharedCoordinateTarget
    {C : Type*} [Countable C] (p : C → ℝ) (s : Bool) : ℝ :=
  ∑' c, p c *
    treeEvaluateAt (DepthOneTree.query () (-1) 1) (fun _ => s)

private def sharedCoordinateArea
    {C : Type*} [Countable C] (p : C → ℝ) : ℝ :=
  boolVariance (sharedCoordinateTarget p) + 0

universe u

private def sharedCoordinateSharpness (C : Type u) [Countable C] : Prop :=
  ∀ (p : C → ℝ),
    validMixture p → (∀ c, 0 < p c) →
      sharedCoordinateArea p = 1

/-- The exact depth-one shared-coordinate theorem uses a fixed mixture target,
root-inclusive conditional variance, a deterministic schedule of global
coordinates, and the same oracle value at every occurrence of a coordinate. -/
def sharpDepthOneSharedCoordinateOracleArea_claim61071 : Prop :=
  (∀ {I Ω C : Type*} [Countable I] [Countable C]
      [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (X : I → Ω → RademacherSign)
      (p : C → ℝ) (trees : C → DepthOneTree I),
      independentRademacher P X →
      validMixture p →
      (∀ c, treeBounded (trees c)) →
      ∃ q : ℕ → Option I,
        scheduleWellFormed p trees q ∧
          rootInclusiveArea P X p trees q ≤ 1) ∧
    (∀ {C : Type*} [Countable C], sharedCoordinateSharpness C)

end MathlibPlus.Open.ResearchFormalization.BatchOracleAreaClaim61071
