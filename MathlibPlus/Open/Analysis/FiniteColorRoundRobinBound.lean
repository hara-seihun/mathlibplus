import Mathlib

namespace MathlibPlus.Open.Analysis.FiniteColorRoundRobinBound

noncomputable section

open MeasureTheory
open Classical
open scoped BigOperators ENNReal

abbrev Sign := Bool

def signValue : Sign → ℝ
  | false => -1
  | true => 1

/-- A deterministic sign-valued coordinate decision tree. -/
inductive SignDecisionTree (I : Type*) where
  | leaf : Sign → SignDecisionTree I
  | query : I → SignDecisionTree I → SignDecisionTree I → SignDecisionTree I

def treeDepth : SignDecisionTree I → ℕ
  | .leaf _ => 0
  | .query _ left right => 1 + max (treeDepth left) (treeDepth right)

def treeEval : SignDecisionTree I → (I → Sign) → Sign
  | .leaf value, _ => value
  | .query coordinate negative positive, oracle =>
      if oracle coordinate then treeEval positive oracle else treeEval negative oracle

/-- All coordinates occurring anywhere in a supplied tree. -/
noncomputable def treeSupport (tree : SignDecisionTree I) : Finset I := by
  classical
  induction tree with
  | leaf _ => exact ∅
  | query coordinate negative positive ihNegative ihPositive =>
      exact insert coordinate (ihNegative ∪ ihPositive)

abbrev BoundedSignDecisionTree (I : Type*) (k : ℕ) :=
  {tree : SignDecisionTree I // treeDepth tree ≤ k}

/-- The law on supplied trees uses the canonical discrete measurable space. -/
noncomputable instance boundedTreeMeasurableSpace (I : Type*) (k : ℕ) :
    MeasurableSpace (BoundedSignDecisionTree I k) := ⊤

abbrev Oracle (I : Type*) := I → Sign
abbrev DecisionFunction (I : Type*) := Oracle I → Sign

noncomputable def treeFunction (tree : BoundedSignDecisionTree I k) :
    DecisionFunction I :=
  fun oracle => treeEval tree.1 oracle

def constantFunction (value : Sign) : DecisionFunction I :=
  fun _ => value

def isConstantFunction (f : DecisionFunction I) : Prop :=
  ∃ value : Sign, ∀ oracle, f oracle = value

def treeIsConstant (tree : BoundedSignDecisionTree I k) : Prop :=
  ∃ value : Sign, ∀ oracle, treeEval tree.1 oracle = value

def treeConstantValue (tree : BoundedSignDecisionTree I k) : Sign :=
  treeEval tree.1 (fun _ => false)

/-- Extensional equivalence classes are the push-forward fibres of the tree law. -/
def treeEquivalent (s t : BoundedSignDecisionTree I k) : Prop :=
  ∀ oracle, treeEval s.1 oracle = treeEval t.1 oracle

noncomputable def functionMass
    (ν : Measure (BoundedSignDecisionTree I k))
    (f : DecisionFunction I) : ℝ≥0∞ :=
  ν {tree | ∀ oracle, treeEval tree.1 oracle = f oracle}

noncomputable def treeFunctionMass
    (ν : Measure (BoundedSignDecisionTree I k))
    (tree : BoundedSignDecisionTree I k) : ℝ≥0∞ :=
  functionMass ν (treeFunction tree)

noncomputable def constantContribution
    (ν : Measure (BoundedSignDecisionTree I k)) : ℝ := by
  classical
  exact ∫ tree, if treeIsConstant tree then
      signValue (treeConstantValue tree) else 0 ∂ν

noncomputable def mixtureValue
    (ν : Measure (BoundedSignDecisionTree I k)) : Oracle I → ℝ :=
  fun oracle => ∫ tree, signValue (treeFunction tree oracle) ∂ν

abbrev PositiveIndex := {index : ℕ // 0 < index}
abbrev IndexIn (J : Set PositiveIndex) := {index : PositiveIndex // index ∈ J}

/-- Exact aggregation of the pushed-forward law, including the two constants. -/
def IsExactAggregation
    (ν : Measure (BoundedSignDecisionTree I k))
    (J : Set PositiveIndex)
    (T : PositiveIndex → DecisionFunction I)
    (weights : PositiveIndex → ℝ)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (c : ℝ) : Prop :=
  (∀ oracle : Oracle I,
    Measurable (fun tree : BoundedSignDecisionTree I k =>
      signValue (treeFunction tree oracle))) ∧
  (∀ f : DecisionFunction I,
    MeasurableSet {tree : BoundedSignDecisionTree I k |
      ∀ oracle, treeEval tree.1 oracle = f oracle}) ∧
  (∀ j, j ∈ J → 0 < weights j) ∧
  (∀ j, j ∈ J → T j = treeFunction (representative j)) ∧
  (∀ ⦃j ell⦄, j ∈ J → ell ∈ J → j ≠ ell → T j ≠ T ell) ∧
  (∀ j, j ∈ J → ¬ isConstantFunction (T j)) ∧
  (∀ f : DecisionFunction I, ¬ isConstantFunction f →
    (0 < functionMass ν f ↔ ∃ j, j ∈ J ∧ T j = f)) ∧
  (∀ j, j ∈ J → weights j = ENNReal.toReal (functionMass ν (T j))) ∧
  c = constantContribution ν ∧
  (∀ oracle, mixtureValue ν oracle =
    c + ∑' j : IndexIn J, weights j.1 * signValue (T j.1 oracle))

/-- Finite-cylinder form of an independent uniform sign oracle. -/
def UniformIndependentSigns {I Ω : Type*} [Countable I]
    [MeasurableSpace Ω] (P : Measure Ω) (O : I → Ω → Sign) : Prop :=
  P Set.univ = 1 ∧
    (∀ i, Measurable (fun ω => O i ω)) ∧
    (∀ (s : Finset I) (assignment : I → Sign),
      MeasurableSet {oracleSample | ∀ i ∈ s, O i oracleSample = assignment i} ∧
        P {oracleSample | ∀ i ∈ s, O i oracleSample = assignment i} =
          ((1 : ENNReal) / 2) ^ s.card)

/-- A proper partition of the positive-mass component indices. -/
def IsIndexPartition (J : Set PositiveIndex) {r : ℕ}
    (parts : Fin r → Set PositiveIndex) : Prop :=
  (∀ color, parts color ⊆ J) ∧
  (⋃ color : Fin r, parts color) = J ∧
    (∀ ⦃color₁ color₂⦄, color₁ ≠ color₂ →
      Disjoint (parts color₁) (parts color₂))

def IsSupportColoring {I : Type*} {k : ℕ}
    (J : Set PositiveIndex) {r : ℕ}
    (parts : Fin r → Set PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k) : Prop :=
  IsIndexPartition J parts ∧
    (∀ ⦃color⦄ ⦃j ell⦄,
      j ∈ parts color → ell ∈ parts color → j ≠ ell →
        Disjoint (treeSupport (representative j).1)
          (treeSupport (representative ell).1))

/-- A non-increasing component order, with the index as the fixed tie-break. -/
def IsOrderedColorSchedule {r : ℕ}
    (J : Set PositiveIndex)
    (parts : Fin r → Set PositiveIndex)
    (weights : PositiveIndex → ℝ)
    (order : Fin r → ℕ → Option PositiveIndex) : Prop :=
  (∀ color n j, order color n = some j → j ∈ parts color ∧ j ∈ J) ∧
  (∀ color j, j ∈ parts color → ∃! n, order color n = some j) ∧
  (∀ color n, order color n = none →
    ∀ m, n ≤ m → order color m = none) ∧
  (∀ color n m j ell,
    order color n = some j → order color m = some ell → n ≤ m →
      weights ell ≤ weights j ∧
        (weights ell = weights j → j.1 ≤ ell.1))

/-- The first known answer to a coordinate in a finite transcript. -/
noncomputable def observedSign (coordinate : I) (transcript : List (I × Sign)) : Option Sign := by
  classical
  exact transcript.foldr
    (fun entry answer => if entry.1 = coordinate then some entry.2 else answer) none

/-- The first unknown coordinate requested by a tree evaluator. -/
noncomputable def treeRequest : SignDecisionTree I → List (I × Sign) → Option I := by
  classical
  intro tree
  induction tree with
  | leaf value =>
      intro transcript
      exact none
  | query coordinate negative positive ihNegative ihPositive =>
      intro transcript
      exact match observedSign coordinate transcript with
      | none => some coordinate
      | some false => ihNegative transcript
      | some true => ihPositive transcript

/-- A color has an unfinished component at the indicated order position. -/
def componentHasRequest {r : ℕ}
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (transcript : List (I × Sign)) (color : Fin r) (position : ℕ) : Prop :=
  ∃ j, order color position = some j ∧
    ∃ coordinate, treeRequest (representative j).1 transcript = some coordinate

/-- The request of the first unfinished component in one color. -/
def firstColorRequest {r : ℕ}
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (transcript : List (I × Sign)) (color : Fin r) (coordinate : I) : Prop :=
  ∃ position j,
    order color position = some j ∧
    treeRequest (representative j).1 transcript = some coordinate ∧
    ∀ earlier, earlier < position →
      ¬ componentHasRequest order representative transcript color earlier

noncomputable def firstActivePosition {r : ℕ}
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (transcript : List (I × Sign)) (color : Fin r) : Option ℕ := by
  classical
  exact if h : ∃ position, componentHasRequest order representative
      transcript color position then
    some (Nat.find h) else none

noncomputable def colorRequest {r : ℕ}
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (transcript : List (I × Sign)) (color : Fin r) : Option I := by
  classical
  exact match firstActivePosition order representative transcript color with
  | none => none
  | some position =>
      match order color position with
      | none => none
      | some j => treeRequest (representative j).1 transcript

def activeColor {r : ℕ}
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (transcript : List (I × Sign)) (color : Fin r) : Prop :=
  ∃ coordinate, colorRequest order representative transcript color = some coordinate

/-- Color `offset` after `cursor` in the cyclic order. -/
def cycleColor (r : ℕ) (hr : 0 < r) (cursor offset : Fin r) : Fin r :=
  ⟨(cursor.val + offset.val) % r, Nat.mod_lt _ hr⟩

def cyclicSuccessor (r : ℕ) (hr : 0 < r) (color : Fin r) : Fin r :=
  cycleColor r hr color ⟨1 % r, Nat.mod_lt _ hr⟩

/-- The first active color encountered from the stored cyclic cursor. -/
noncomputable def nextActiveColor {r : ℕ}
    (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (transcript : List (I × Sign)) (cursor : Fin r) : Option (Fin r) := by
  classical
  let candidates : Finset (Fin r) :=
    (Finset.univ : Finset (Fin r)).filter (fun offset =>
      activeColor order representative transcript
        (cycleColor r hr cursor offset))
  exact if h : candidates.Nonempty then
    some (cycleColor r hr cursor (candidates.min' h)) else none

structure RoundRobinState (I : Type*) (r : ℕ) where
  transcript : List (I × Sign)
  cursor : Fin r

noncomputable def roundRobinStep {I Ω : Type*} {r : ℕ}
    (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (O : I → Ω → Sign)
    (state : RoundRobinState I r) (sample : Ω) : RoundRobinState I r :=
  match nextActiveColor hr order representative state.transcript state.cursor with
  | none => state
  | some color =>
      match colorRequest order representative state.transcript color with
      | none =>
          { transcript := state.transcript
            cursor := cyclicSuccessor r hr color }
      | some coordinate =>
          { transcript := state.transcript ++
              [(coordinate, O coordinate sample)]
            cursor := cyclicSuccessor r hr color }

noncomputable def roundRobinStateAt {I Ω : Type*} {r : ℕ}
    (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (O : I → Ω → Sign) (sample : Ω) : ℕ → RoundRobinState I r
  | 0 =>
      { transcript := []
        cursor := ⟨0, Nat.zero_lt_of_lt hr⟩ }
  | m + 1 => roundRobinStep hr order representative O
      (roundRobinStateAt hr order representative O sample m) sample

noncomputable def roundRobinTranscriptAt {I Ω : Type*} {r : ℕ}
    (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (O : I → Ω → Sign) (sample : Ω) (m : ℕ) : List (I × Sign) :=
  (roundRobinStateAt hr order representative O sample m).transcript

/-- A transcript cell for the actual revealed coordinate answers. -/
def transcriptCell {I Ω : Type*}
    (O : I → Ω → Sign) (transcript : List (I × Sign)) : Set Ω :=
  {sample | ∀ entry ∈ transcript, O entry.1 sample = entry.2}

def constantOnCell {Ω : Type*} (f : Ω → ℝ) (C : Set Ω) : Prop :=
  ∀ ⦃x y : Ω⦄, x ∈ C → y ∈ C → f x = f y

def conditionalMean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else (∫ x in C, f x ∂P) / (P C).toReal

def conditionalVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else
    (∫ x in C, (f x - conditionalMean P f C) ^ 2 ∂P) / (P C).toReal

noncomputable def posteriorVariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ := by
  classical
  exact if constantOnCell f C then 0 else conditionalVariance P f C

noncomputable def mixtureOnSample {I Ω : Type*} {k : ℕ}
    (ν : Measure (BoundedSignDecisionTree I k))
    (O : I → Ω → Sign) : Ω → ℝ :=
  fun sample => mixtureValue ν (fun i => O i sample)

noncomputable def roundRobinArea {I Ω : Type*} [MeasurableSpace Ω] {r k : ℕ}
    (P : Measure Ω) (ν : Measure (BoundedSignDecisionTree I k))
    (O : I → Ω → Sign) (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k) : ℝ :=
  ∑' m : ℕ, ∫ sample,
    posteriorVariance P (mixtureOnSample ν O)
      (transcriptCell O (roundRobinTranscriptAt hr order representative O sample m)) ∂P

def roundRobinLegality {I Ω : Type*} {r k : ℕ}
    (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (O : I → Ω → Sign) : Prop :=
  ∀ sample m,
    let state := roundRobinStateAt hr order representative O sample m
    (state.transcript.map Prod.fst).Nodup ∧
      (match nextActiveColor hr order representative
          state.transcript state.cursor with
       | none => True
       | some color =>
           ∃ coordinate,
             colorRequest order representative state.transcript color = some coordinate ∧
               coordinate ∉ state.transcript.map Prod.fst)

/-- The stateful cyclic policy, its filtration, terminal behavior, and area bound. -/
def RoundRobinConclusion {I Ω : Type*} [MeasurableSpace Ω]
    {r k : ℕ} (P : Measure Ω)
    (ν : Measure (BoundedSignDecisionTree I k))
    (O : I → Ω → Sign)
    (J : Set PositiveIndex) (parts : Fin r → Set PositiveIndex)
    (weights : PositiveIndex → ℝ)
    (representative : PositiveIndex → BoundedSignDecisionTree I k)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (hr : 0 < r)
    (order : Fin r → ℕ → Option PositiveIndex) : Prop :=
  IsOrderedColorSchedule J parts weights order ∧
  roundRobinLegality hr order representative O ∧
  (∀ step,
    F.seq step =
      MeasurableSpace.comap
        (fun sample => roundRobinTranscriptAt hr order representative O sample step)
        (⊤ : MeasurableSpace (List (I × Sign)))) ∧
  @Measurable Ω ℝ (⨆ step : ℕ, F.seq step)
    (inferInstance : MeasurableSpace ℝ) (mixtureOnSample ν O) ∧
  (J.Finite →
    ∀ sample, ∃ terminal, ∀ step, terminal ≤ step →
      roundRobinTranscriptAt hr order representative O sample step =
        roundRobinTranscriptAt hr order representative O sample terminal ∧
      nextActiveColor hr order representative
        (roundRobinTranscriptAt hr order representative O sample step)
        ((roundRobinStateAt hr order representative O sample step).cursor) = none) ∧
  roundRobinArea P ν O hr order representative ≤
    (r : ℝ) ^ 2 * (k : ℝ) *
      ∑ color : Fin r,
        (∑' j : IndexIn (parts color), weights j.1) ^ 2 ∧
  (r : ℝ) ^ 2 * (k : ℝ) *
      ∑ color : Fin r,
        (∑' j : IndexIn (parts color), weights j.1) ^ 2 ≤
    (r : ℝ) ^ 2 * (k : ℝ)

/-- Bipartiteness of the support-intersection graph for the chosen representatives. -/
def IsBipartiteSupportIntersection {I : Type*} {k : ℕ}
    (J : Set PositiveIndex)
    (representative : PositiveIndex → BoundedSignDecisionTree I k) : Prop :=
  ∃ parts : Fin 2 → Set PositiveIndex,
    IsSupportColoring J parts representative

/-- Finite-color round-robin bound with the explicit skip-finished-colors cursor. -/
def finiteColorRoundRobinBound (I : Type*) [Countable I] : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (O : I → Ω → Sign),
    UniformIndependentSigns P O →
    ∀ (k : ℕ), 0 < k →
      ∀ (ν : Measure (BoundedSignDecisionTree I k)), ν Set.univ = 1 →
        ∀ (J : Set PositiveIndex)
          (T : PositiveIndex → DecisionFunction I)
          (weights : PositiveIndex → ℝ)
          (representative : PositiveIndex → BoundedSignDecisionTree I k)
          (c : ℝ),
          IsExactAggregation ν J T weights representative c →
            (∀ (r : ℕ), 0 < r →
              ∀ (parts : Fin r → Set PositiveIndex),
                IsSupportColoring J parts representative →
                  ∃ (order : Fin r → ℕ → Option PositiveIndex)
                    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)),
                    ∃ hr : 0 < r,
                      RoundRobinConclusion P ν O J parts weights representative
                        F hr order) ∧
            (IsBipartiteSupportIntersection J representative →
              ∃ (parts : Fin 2 → Set PositiveIndex),
                IsSupportColoring J parts representative ∧
                ∃ (order : Fin 2 → ℕ → Option PositiveIndex)
                  (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
                  (hr : 0 < 2),
                  RoundRobinConclusion P ν O J parts weights representative
                    F hr order ∧
                  roundRobinArea P ν O hr order representative ≤ 4 * (k : ℝ))

end
end MathlibPlus.Open.Analysis.FiniteColorRoundRobinBound
