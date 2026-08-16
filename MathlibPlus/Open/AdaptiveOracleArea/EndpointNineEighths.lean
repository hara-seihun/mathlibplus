import Mathlib

namespace MathlibPlus.Open.AdaptiveOracleArea

abbrev SignState := Fin 4 → Bool
abbrev Component := Bool

structure SignedCoordinate where
  index : Fin 4
  negate : Bool
deriving DecidableEq

structure DepthTwoTree where
  selector : Fin 4
  negativeLeaf : SignedCoordinate
  positiveLeaf : SignedCoordinate
deriving DecidableEq

def signValue (b : Bool) : ℚ :=
  if b = false then -1 else 1

def coordinateValue (x : SignState) (i : Fin 4) : ℚ :=
  signValue (x i)

def signedCoordinateValue (x : SignState) (c : SignedCoordinate) : ℚ :=
  if c.negate = true then -coordinateValue x c.index else coordinateValue x c.index

def treeValue (t : DepthTwoTree) (x : SignState) : ℚ :=
  if x t.selector = false then
    signedCoordinateValue x t.negativeLeaf
  else
    signedCoordinateValue x t.positiveLeaf

def aCoordinate : SignedCoordinate :=
  { index := (1 : Fin 4), negate := true }

def bCoordinate : SignedCoordinate :=
  { index := (3 : Fin 4), negate := false }

def tree0 : DepthTwoTree :=
  { selector := (0 : Fin 4), negativeLeaf := aCoordinate, positiveLeaf := bCoordinate }

def tree2 : DepthTwoTree :=
  { selector := (2 : Fin 4), negativeLeaf := aCoordinate, positiveLeaf := bCoordinate }

def legalDepthTwo (t : DepthTwoTree) : Prop :=
  t.selector ≠ t.negativeLeaf.index ∧ t.selector ≠ t.positiveLeaf.index

def componentTree (c : Component) : DepthTwoTree :=
  if c = false then tree0 else tree2

def selectedLeafCoordinate (c : Component) (x : SignState) : Fin 4 :=
  let t := componentTree c
  if x t.selector = false then t.negativeLeaf.index else t.positiveLeaf.index

def componentValue (c : Component) (x : SignState) : ℚ :=
  treeValue (componentTree c) x

def A (x : SignState) : ℚ :=
  signedCoordinateValue x aCoordinate

def B (x : SignState) : ℚ :=
  signedCoordinateValue x bCoordinate

def T0 (x : SignState) : ℚ :=
  componentValue false x

def T2 (x : SignState) : ℚ :=
  componentValue true x

def mu (x : SignState) : ℚ :=
  (T0 x + T2 x) / 2

structure StepTranscript where
  component : Component
  selectorIndex : Fin 4
  selectorAnswer : Bool
  leafIndex : Fin 4
  leafAnswer : Bool
deriving DecidableEq

abbrev SamplePath (d : Nat) := Fin d → Component
abbrev JointState (d : Nat) := SignState × SamplePath d
abbrev BlockTranscript (d : Nat) := Fin d → StepTranscript

def sampledTranscript (d : Nat) (z : JointState d) : BlockTranscript d :=
  fun k =>
    let x := z.1
    let c := z.2 k
    let t := componentTree c
    { component := c
      selectorIndex := t.selector
      selectorAnswer := x t.selector
      leafIndex := selectedLeafCoordinate c x
      leafAnswer := x (selectedLeafCoordinate c x) }

def uniformAverage {α : Type} [Fintype α] (f : α → ℚ) : ℚ :=
  (∑ a : α, f a) / (Fintype.card α : ℚ)

def fiberCount {S T : Type} [Fintype S] [DecidableEq T]
    (observation : S → T) (transcript : T) : ℚ :=
  ∑ s : S, if observation s = transcript then 1 else 0

def fiberFirstMoment {S T : Type} [Fintype S] [DecidableEq T]
    (value : S → ℚ) (observation : S → T) (transcript : T) : ℚ :=
  ∑ s : S, if observation s = transcript then value s else 0

def fiberSecondMoment {S T : Type} [Fintype S] [DecidableEq T]
    (value : S → ℚ) (observation : S → T) (transcript : T) : ℚ :=
  ∑ s : S, if observation s = transcript then value s * value s else 0

def conditionalVariance {S T : Type} [Fintype S] [DecidableEq T]
    (value : S → ℚ) (observation : S → T) (transcript : T) : ℚ :=
  let count := fiberCount observation transcript
  let first := fiberFirstMoment value observation transcript
  let second := fiberSecondMoment value observation transcript
  second / count - (first / count) * (first / count)

def expectedPosteriorRisk {S T : Type} [Fintype S] [DecidableEq T]
    (value : S → ℚ) (observation : S → T) : ℚ :=
  uniformAverage (fun s => conditionalVariance value observation (observation s))

def blockEndpointRisk (d : Nat) : ℚ :=
  expectedPosteriorRisk (fun z : JointState d => mu z.1) (sampledTranscript d)

def R (d : Nat) : ℚ :=
  blockEndpointRisk d

structure ActualQuery where
  index : Fin 4
  answer : Bool
deriving DecidableEq

structure ActualTranscript where
  firstComponent : Option Component
  secondComponent : Option Component
  freshQueries : Fin 4 → Option ActualQuery
deriving DecidableEq

abbrev ActualState := SignState × Component

def revealOrder (x : SignState) (c : Component) : List (Fin 4) :=
  let first := componentTree c
  let second := componentTree (Bool.not c)
  let firstLeaf := selectedLeafCoordinate c x
  let secondLeaf := selectedLeafCoordinate (Bool.not c) x
  if secondLeaf = firstLeaf then
    [first.selector, firstLeaf, second.selector]
  else
    [first.selector, firstLeaf, second.selector, secondLeaf]

def coordinateAt? : List (Fin 4) → Nat → Option (Fin 4)
  | [], _ => none
  | i :: _, 0 => some i
  | _ :: rest, n + 1 => coordinateAt? rest n

def actualTranscript (m : Nat) (x : SignState) (c : Component) : ActualTranscript :=
  { firstComponent := if m = 0 then none else some c
    secondComponent := if 3 ≤ m then some (Bool.not c) else none
    freshQueries := fun k =>
      if k.val < m then
        match coordinateAt? (revealOrder x c) k.val with
        | some i => some { index := i, answer := x i }
        | none => none
      else
        none }

def actualObservation (m : Nat) (z : ActualState) : ActualTranscript :=
  actualTranscript m z.1 z.2

def actualRisk (m : Nat) : ℚ :=
  expectedPosteriorRisk (fun z : ActualState => mu z.1) (actualObservation m)

def actualPolicyComplete : Prop :=
  (∀ x c, (revealOrder x c).Nodup) ∧
  (∀ x c, (revealOrder x c).length ≤ 4) ∧
  (∀ z z', actualObservation 4 z = actualObservation 4 z' → mu z.1 = mu z'.1) ∧
  (∀ m z, 4 ≤ m → actualObservation m z = actualObservation 4 z)

def answerAdaptivePathsHaveSampledTranscriptEndpointAreaNineEighths : Prop :=
  legalDepthTwo tree0 ∧
  legalDepthTwo tree2 ∧
  R 0 = (3 : ℚ) / 4 ∧
  (∀ d : Nat, 1 ≤ d → R d = 3 / (2 : ℚ) ^ (d + 3)) ∧
  (∑' d : Nat, (R d : ℝ)) = (9 : ℝ) / 8 ∧
  (∑' d : Nat, (R d : ℝ)) > 1 ∧
  actualPolicyComplete ∧
  actualRisk 0 = (3 : ℚ) / 4 ∧
  actualRisk 1 = (3 : ℚ) / 4 ∧
  actualRisk 2 = (3 : ℚ) / 16 ∧
  actualRisk 3 = (1 : ℚ) / 8 ∧
  (∀ m : Nat, 4 ≤ m → actualRisk m = 0) ∧
  actualRisk 0 + actualRisk 1 + actualRisk 2 + actualRisk 3 = (29 : ℚ) / 16 ∧
  (∑' m : Nat, (actualRisk m : ℝ)) = (29 : ℝ) / 16

end MathlibPlus.Open.AdaptiveOracleArea
