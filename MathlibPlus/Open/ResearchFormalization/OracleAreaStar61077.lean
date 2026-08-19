import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaStar61077

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

abbrev Sign := Bool
abbrev Coordinate := Fin 3
abbrev State := Coordinate → Sign
abbrev Transcript := Coordinate → Option Sign

def signValue : Sign → ℝ
  | false => -1
  | true => 1

def stateSpace : Finset State := Finset.univ

def uniformAverage (f : State → ℝ) : ℝ :=
  (∑ ω : State, f ω) / (Fintype.card State : ℝ)

def T₁ (ω : State) : ℝ :=
  (signValue (ω 0) + signValue (ω 2)) / 2 +
    signValue (ω 1) *
      (signValue (ω 2) - signValue (ω 0)) / 2

def T₂ (ω : State) : ℝ :=
  (signValue (ω 0) + signValue (ω 1)) / 2 +
    signValue (ω 2) *
      (signValue (ω 1) - signValue (ω 0)) / 2

def mixtureTarget (ω : State) : ℝ := (T₁ ω - T₂ ω) / 2

inductive DecisionTree (ι : Type) where
  | leaf (value : Sign)
  | query (coordinate : ι) (negative positive : DecisionTree ι)

def DecisionTree.evaluate : DecisionTree ι → (ι → Sign) → Sign
  | .leaf value, _ => value
  | .query coordinate negative positive, ω =>
      if ω coordinate then
        DecisionTree.evaluate positive ω
      else
        DecisionTree.evaluate negative ω

def DecisionTree.depth : DecisionTree ι → ℕ
  | .leaf _ => 0
  | .query _ negative positive =>
      1 + max negative.depth positive.depth

def DecisionTree.root : DecisionTree ι → Option ι
  | .leaf _ => none
  | .query coordinate _ _ => some coordinate

def identityTree (c : Coordinate) : DecisionTree Coordinate :=
  .query c (.leaf false) (.leaf true)

def tree₁ : DecisionTree Coordinate :=
  .query 1 (identityTree 0) (identityTree 2)

def tree₂ : DecisionTree Coordinate :=
  .query 2 (identityTree 0) (identityTree 1)

/-- A coordinate is a depth-reducing first query for a tree when the tree's
Boolean function has a first-query realization whose two residual trees have
depth at most one. -/
def depthReducingFirstQuery (T : DecisionTree Coordinate)
    (c : Coordinate) : Prop :=
  ∃ negative positive : DecisionTree Coordinate,
    negative.depth ≤ 1 ∧ positive.depth ≤ 1 ∧
      ∀ ω : State,
        T.evaluate ω =
          (DecisionTree.query c negative positive).evaluate ω

def emptyTranscript : Transcript := fun _ => none

def observe (h : Transcript) (c : Coordinate) (s : Sign) : Transcript :=
  Function.update h c (some s)

def compatible (h : Transcript) (ω : State) : Prop :=
  ∀ c, match h c with
    | none => True
    | some s => ω c = s

noncomputable def compatibleStates (h : Transcript) : Finset State :=
  stateSpace.filter (fun ω => compatible h ω)

noncomputable def posteriorMean (h : Transcript) : ℝ :=
  (∑ ω ∈ compatibleStates h, mixtureTarget ω) /
    (compatibleStates h).card

noncomputable def posteriorVariance (h : Transcript) : ℝ :=
  (∑ ω ∈ compatibleStates h,
      (mixtureTarget ω - posteriorMean h) ^ 2) /
    (compatibleStates h).card

def targetMeasurable (h : Transcript) : Prop :=
  ∀ ω₁ ∈ compatibleStates h, ∀ ω₂ ∈ compatibleStates h,
    mixtureTarget ω₁ = mixtureTarget ω₂

structure CoordinatePolicy where
  next : Transcript → Option Coordinate

def legalPolicy (p : CoordinatePolicy) : Prop :=
  (∀ h c, p.next h = some c →
    h c = none ∧ ¬targetMeasurable h) ∧
    (∀ h, p.next h = none ↔ targetMeasurable h)

def policyTranscript (p : CoordinatePolicy) (ω : State) : ℕ → Transcript
  | 0 => emptyTranscript
  | m + 1 =>
      let h := policyTranscript p ω m
      match p.next h with
      | none => h
      | some c => observe h c (ω c)

noncomputable def expectedVarianceAt
    (p : CoordinatePolicy) (m : ℕ) : ℝ :=
  (∑ ω : State, posteriorVariance (policyTranscript p ω m)) /
    stateSpace.card

noncomputable def policyArea (p : CoordinatePolicy) : ℝ :=
  ∑ m : Fin 4, expectedVarianceAt p m.1

noncomputable def optimalBellmanArea : ℝ :=
  sInf {a : ℝ | ∃ p : CoordinatePolicy, legalPolicy p ∧ policyArea p = a}

def rFirstPolicy : CoordinatePolicy :=
  { next := fun h =>
      if h 0 = none then
        some 0
      else if h 0 = some true then
        if h 1 = none then some 1
        else if h 2 = none then some 2
        else none
      else none }

def walshCharacter (S : Finset Coordinate) (ω : State) : ℝ :=
  ∏ i ∈ S, signValue (ω i)

def walshCoefficient (S : Finset Coordinate) : ℝ :=
  uniformAverage (fun ω => mixtureTarget ω * walshCharacter S ω)

def quadraticStarSupport : Prop :=
  ∀ S : Finset Coordinate,
    S.card = 2 →
      (walshCoefficient S ≠ 0 ↔
        S = {0, 1} ∨ S = {0, 2})

/-- Claim 61077: the two supplied rooted selectors have no common
componentwise depth-reducing first query, while their fixed mixture is the
star-cancelled target with the stated legal and optimal areas. -/
def claim61077 : Prop :=
  stateSpace.card = 8 ∧
    tree₁.depth = 2 ∧
    tree₂.depth = 2 ∧
    tree₁.root = some 1 ∧
    tree₂.root = some 2 ∧
    (∀ c : Coordinate,
      ¬(depthReducingFirstQuery tree₁ c ∧
        depthReducingFirstQuery tree₂ c)) ∧
    (∀ ω : State,
      signValue (tree₁.evaluate ω) =
          (if ω 1 then signValue (ω 2) else signValue (ω 0)) ∧
        signValue (tree₂.evaluate ω) =
          (if ω 2 then signValue (ω 1) else signValue (ω 0)) ∧
        mixtureTarget ω =
          (signValue (ω 2) - signValue (ω 1)) *
            (1 + signValue (ω 0)) / 4) ∧
    quadraticStarSupport ∧
    legalPolicy rFirstPolicy ∧
    policyArea rFirstPolicy = 5 / 8 ∧
    optimalBellmanArea = 9 / 16

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaStar61077
