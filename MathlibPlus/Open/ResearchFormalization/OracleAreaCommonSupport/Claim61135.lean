import MathlibPlus.Open.Analysis.AdaptiveTranscriptWalshKernel

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaCommonSupport

open MeasureTheory
open MathlibPlus.Open.Analysis
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable

abbrev RademacherOracle (I : Type*) := I → ℝ
abbrev Transcript (I : Type*) := I → Option ℝ

/-- The leaf outputs of a component tree are signs; repeated queries are not
excluded, since the common-support hypothesis concerns every queried node. -/
def signValuedTree {I : Type*} : AdaptiveRevealTree I → Prop
  | .leaf output => output = -1 ∨ output = 1
  | .query _ negative positive =>
      signValuedTree negative ∧ signValuedTree positive

/-- All coordinates occurring anywhere in a component decision tree. -/
noncomputable def treeSupport {I : Type*} : AdaptiveRevealTree I → Finset I
  | .leaf _ => ∅
  | .query coordinate negative positive =>
      insert coordinate (treeSupport negative ∪ treeSupport positive)

/-- The fixed mixture target, with its constant term and countable component
series displayed explicitly. -/
def mixtureTarget {I J : Type*} [Countable J]
    (c : ℝ) (weights : J → ℝ)
    (trees : J → AdaptiveRevealTree I) : RademacherOracle I → ℝ :=
  fun ω => c + ∑' j : J, weights j * adaptiveTreeRun (trees j) ω

/-- An order enumerates exactly the finite support set. -/
def orderEnumerates {I : Type*} (D : Finset I)
    (order : Fin D.card → I) : Prop :=
  Function.Injective order ∧
    ∀ i, i ∈ D ↔ ∃ r : Fin D.card, order r = i

/-- The deterministic action at time `m`: reveal the `m`th coordinate in the
fixed order, and take no action after all coordinates have been revealed. -/
def fixedRevealAction {I : Type*} (D : Finset I)
    (order : Fin D.card → I) (m : ℕ) : Option I :=
  if h : m < D.card then some (order ⟨m, h⟩) else none

/-- The transcript after `m` actions of the fixed-order policy. -/
def fixedRevealHistory {I : Type*} (D : Finset I)
    (order : Fin D.card → I) (ω : RademacherOracle I) (m : ℕ) : Transcript I :=
  fun i =>
    if ∃ r : Fin D.card, r.val < min m D.card ∧ order r = i then
      some (ω i)
    else none

/-- Compatibility of an oracle with a revealed-coordinate transcript. -/
def transcriptCompatible {I : Type*}
    (history : Transcript I) (ω : RademacherOracle I) : Prop :=
  ∀ i v, history i = some v → ω i = v

/-- The cylinder of oracles compatible with the actual transcript. -/
def fixedRevealCell {I : Type*} (D : Finset I)
    (order : Fin D.card → I) (ω : RademacherOracle I) (m : ℕ) : Set (RademacherOracle I) :=
  {y | transcriptCompatible (fixedRevealHistory D order ω m) y}

/-- Posterior variance at the transcript after `m` fixed-order reveals. -/
def fixedRevealPosteriorVariance {I : Type*}
    (P : Measure (RademacherOracle I)) (μ : RademacherOracle I → ℝ)
    (D : Finset I) (order : Fin D.card → I)
    (ω : RademacherOracle I) (m : ℕ) : ℝ :=
  adaptiveConditionalVariance P μ (fixedRevealCell D order ω m)

/-- Root-inclusive cumulative posterior-variance area, with the terminal
transcript retained for all later natural-number times. -/
noncomputable def fixedRevealArea {I : Type*}
    (P : Measure (RademacherOracle I)) (μ : RademacherOracle I → ℝ)
    (D : Finset I) (order : Fin D.card → I) : ℝ :=
  ∑' m : ℕ, ∫ ω,
    fixedRevealPosteriorVariance P μ D order ω m ∂P

/-- Legality of the fixed schedule: every action is a fresh coordinate in `D`. -/
def fixedRevealActionLegal {I : Type*} (D : Finset I)
    (order : Fin D.card → I) : Prop :=
  ∀ m i, fixedRevealAction D order m = some i →
    i ∈ D ∧ ∀ r : Fin D.card, r.val < m → order r ≠ i

/-- Every ordered coordinate is revealed at its own time, and the schedule
covers the whole common support. -/
def fixedRevealEnumerates {I : Type*} (D : Finset I)
    (order : Fin D.card → I) : Prop :=
  (∀ r : Fin D.card,
    fixedRevealAction D order r.val = some (order r)) ∧
    (∀ i, i ∈ D → ∃ m < D.card,
      fixedRevealAction D order m = some i)

/-- The policy has stopped once the last coordinate has been revealed. -/
def fixedRevealStops {I : Type*} (D : Finset I)
    (order : Fin D.card → I) : Prop :=
  ∀ m, D.card ≤ m → fixedRevealAction D order m = none

/-- Measurability of a target from the finite coordinate set `D`, written as
constancy on every pair of oracles having the same `D`-coordinates. -/
def targetDeterminedByD {I : Type*} (D : Finset I)
    (μ : RademacherOracle I → ℝ) : Prop :=
  ∀ x y, (∀ i, i ∈ D → x i = y i) → μ x = μ y

/-- The terminal transcript determines the fixed target, including at every
later time at which the stopped transcript is held constant. -/
def fixedRevealTerminallyDetermines {I : Type*} (D : Finset I)
    (order : Fin D.card → I) (μ : RademacherOracle I → ℝ) : Prop :=
  ∀ m ω y, D.card ≤ m →
    transcriptCompatible (fixedRevealHistory D order ω m) y →
      μ y = μ ω

/-- The later posterior-variance terms vanish after the last reveal. -/
def fixedRevealTerminalVarianceZero {I : Type*}
    (P : Measure (RademacherOracle I)) (μ : RademacherOracle I → ℝ)
    (D : Finset I) (order : Fin D.card → I) : Prop :=
  ∀ m ω, D.card ≤ m →
    fixedRevealPosteriorVariance P μ D order ω m = 0

/-- Claim 61135: a common finite coordinate support gives the deterministic
fixed-order policy and the root-inclusive bound `d L^2 ≤ d ≤ k`, for finite or
countable component families and independent uniform Rademacher coordinates. -/
def claim61135_commonSupportArea : Prop :=
  ∀ {I J : Type*} [Countable I] [Countable J]
    (P : Measure (RademacherOracle I))
    (c L : ℝ) (k : ℕ)
    (weights : J → ℝ)
    (trees : J → AdaptiveRevealTree I)
    (D : Finset I),
    fairIndependentRademacher P →
    (∀ j, 0 ≤ weights j) →
    HasSum weights L →
    L ≤ 1 →
    D.card ≤ k →
    (∀ j,
      signValuedTree (trees j) ∧
        adaptiveTreeDepth (trees j) ≤ k ∧
        treeSupport (trees j) ⊆ D) →
    ∀ order : Fin D.card → I,
      orderEnumerates D order →
      let μ := mixtureTarget c weights trees
      (∀ ω, Summable
        (fun j => |weights j * adaptiveTreeRun (trees j) ω|)) ∧
      targetDeterminedByD D μ ∧
      fixedRevealActionLegal D order ∧
      fixedRevealEnumerates D order ∧
      fixedRevealStops D order ∧
      fixedRevealTerminallyDetermines D order μ ∧
      fixedRevealTerminalVarianceZero P μ D order ∧
      fixedRevealArea P μ D order ≤
        (D.card : ℝ) * L ^ 2 ∧
      (D.card : ℝ) * L ^ 2 ≤ (D.card : ℝ) ∧
      (D.card : ℝ) ≤ (k : ℝ)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaCommonSupport
