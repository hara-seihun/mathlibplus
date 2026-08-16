import Mathlib

noncomputable section
open BigOperators

namespace MathlibPlus.Open.AdaptiveOracleArea

abbrev Coordinate := Fin 3

def coordA : Coordinate := 0

def coordE : Coordinate := 1

def coordB : Coordinate := 2

abbrev Sign := Bool

def signValue : Sign → ℝ
  | false => -1
  | true => 1

def State := Coordinate → Sign

def Transcript := Coordinate → Option Sign

noncomputable def stateSpace : Finset State := by
  classical
  exact
    ([![false, false, false], ![false, false, true],
      ![false, true, false], ![false, true, true],
      ![true, false, false], ![true, false, true],
      ![true, true, false], ![true, true, true]] : List State).toFinset

def uniformStateAverage (f : State → ℝ) : ℝ :=
  (∑ ω ∈ stateSpace, f ω) / (stateSpace.card : ℝ)

def componentAE (ω : State) : ℝ :=
  signValue (ω coordA) * signValue (ω coordE)

def componentB (ω : State) : ℝ := signValue (ω coordB)

def q (p : ℝ) : ℝ := 1 - p

def target (p : ℝ) (ω : State) : ℝ :=
  p * componentAE ω + q p * componentB ω

inductive CoordinateTree
  | leaf (value : Sign)
  | query (coordinate : Coordinate) (negative positive : CoordinateTree)

def treeDepth : CoordinateTree → Nat
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max (treeDepth negative) (treeDepth positive)

def evaluateTree : CoordinateTree → State → Sign
  | .leaf value, _ => value
  | .query c negative positive, ω =>
      match ω c with
      | false => evaluateTree negative ω
      | true => evaluateTree positive ω

def aeTree : CoordinateTree :=
  .query coordA
    (.query coordE (.leaf true) (.leaf false))
    (.query coordE (.leaf false) (.leaf true))

def bTree : CoordinateTree :=
  .query coordB (.leaf false) (.leaf true)

def emptyTranscript : Transcript := fun _ => none

def observe (h : Transcript) (c : Coordinate) (s : Sign) : Transcript :=
  Function.update h c (some s)

def transcriptAfterA (ω : State) : Transcript :=
  observe emptyTranscript coordA (ω coordA)

def transcriptAfterAE (ω : State) : Transcript :=
  observe (transcriptAfterA ω) coordE (ω coordE)

def transcriptAfterAEB (ω : State) : Transcript :=
  observe (transcriptAfterAE ω) coordB (ω coordB)

def transcriptAfterB (ω : State) : Transcript :=
  observe emptyTranscript coordB (ω coordB)

def transcriptAfterBA (ω : State) : Transcript :=
  observe (transcriptAfterB ω) coordA (ω coordA)

def transcriptAfterBAE (ω : State) : Transcript :=
  observe (transcriptAfterBA ω) coordE (ω coordE)

def compatible (h : Transcript) (ω : State) : Prop :=
  ∀ c, match h c with
    | none => True
    | some s => ω c = s

noncomputable def compatibleStates (h : Transcript) : Finset State := by
  classical
  exact stateSpace.filter (fun ω => compatible h ω)

def posteriorMean (p : ℝ) (h : Transcript) : ℝ :=
  (∑ ω ∈ compatibleStates h, target p ω) /
    (compatibleStates h).card

def posteriorVariance (p : ℝ) (h : Transcript) : ℝ :=
  (∑ ω ∈ compatibleStates h,
      (target p ω - posteriorMean p h) ^ 2) /
    (compatibleStates h).card

def conditionalProbability (h : Transcript) (c : Coordinate) (s : Sign) : ℝ :=
  (compatibleStates (observe h c s)).card /
    (compatibleStates h).card

def expectedPosteriorVariance (p : ℝ) (h : Transcript)
    (c : Coordinate) : ℝ :=
  ∑ s : Sign,
    conditionalProbability h c s *
      posteriorVariance p (observe h c s)

def varianceDrop (p : ℝ) (h : Transcript) (c : Coordinate) : ℝ :=
  posteriorVariance p h - expectedPosteriorVariance p h c

def restrictedTargetNonconstant (p : ℝ) (h : Transcript)
    (c : Coordinate) : Prop :=
  ∃ ω₁ ∈ compatibleStates h, ∃ ω₂ ∈ compatibleStates h,
    (∀ d, d ≠ c → ω₁ d = ω₂ d) ∧
    ω₁ c ≠ ω₂ c ∧ target p ω₁ ≠ target p ω₂

def legalCoordinate (p : ℝ) (h : Transcript) (c : Coordinate) : Prop :=
  h c = none ∧ restrictedTargetNonconstant p h c

def deltaMaximizer (p : ℝ) (h : Transcript) (c : Coordinate) : Prop :=
  legalCoordinate p h c ∧
    ∀ d, legalCoordinate p h d →
      varianceDrop p h d ≤ varianceDrop p h c

noncomputable def myopicChoice (p : ℝ) (h : Transcript) : Option Coordinate := by
  classical
  exact
    if deltaMaximizer p h coordA then some coordA
    else if deltaMaximizer p h coordE then some coordE
    else if deltaMaximizer p h coordB then some coordB
    else none

def targetMeasurable (p : ℝ) (h : Transcript) : Prop :=
  ∀ ω₁ ∈ compatibleStates h, ∀ ω₂ ∈ compatibleStates h,
    target p ω₁ = target p ω₂

def myopicArea (p : ℝ) : ℝ :=
  uniformStateAverage (fun ω =>
    posteriorVariance p emptyTranscript +
    posteriorVariance p (transcriptAfterB ω) +
    posteriorVariance p (transcriptAfterBA ω))

def fixedOrderArea (p : ℝ) : ℝ :=
  uniformStateAverage (fun ω =>
    posteriorVariance p emptyTranscript +
    posteriorVariance p (transcriptAfterA ω) +
    posteriorVariance p (transcriptAfterAE ω))

def adaptiveOracleAreaSharp : Prop :=
  (stateSpace.card = 8) ∧
  treeDepth aeTree = 2 ∧
  treeDepth bTree = 1 ∧
  (∀ ω : State,
    signValue (evaluateTree aeTree ω) = componentAE ω ∧
    signValue (evaluateTree bTree ω) = componentB ω) ∧
  (∀ p : ℝ, 0 < p → p < 1 →
    (∀ ω : State,
      target p ω = p * componentAE ω + q p * componentB ω) ∧
    (∀ ω : State,
      myopicChoice p emptyTranscript = some coordB ∧
      myopicChoice p (transcriptAfterB ω) = some coordA ∧
      myopicChoice p (transcriptAfterBA ω) = some coordE ∧
      myopicChoice p (transcriptAfterBAE ω) = none ∧
      targetMeasurable p (transcriptAfterBAE ω) ∧
      ¬ targetMeasurable p (transcriptAfterB ω) ∧
      ¬ targetMeasurable p (transcriptAfterBA ω)) ∧
    (∀ ω : State,
      legalCoordinate p emptyTranscript coordA ∧
      legalCoordinate p (transcriptAfterA ω) coordE ∧
      legalCoordinate p (transcriptAfterAE ω) coordB ∧
      targetMeasurable p (transcriptAfterAEB ω) ∧
      ¬ targetMeasurable p (transcriptAfterAE ω)) ∧
    ((1 + Real.sqrt 5) / 4 < p →
      myopicArea p = 3 * p ^ 2 + q p ^ 2 ∧
      myopicArea p > 2 ∧
      fixedOrderArea p = 2 * p ^ 2 + 3 * q p ^ 2 ∧
      fixedOrderArea p < 2)) ∧
  (myopicArea (5 / 6 : ℝ) = 19 / 9 ∧
    fixedOrderArea (5 / 6 : ℝ) = 53 / 36)

end MathlibPlus.Open.AdaptiveOracleArea
