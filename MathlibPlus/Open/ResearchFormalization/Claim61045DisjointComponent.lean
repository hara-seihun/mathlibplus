import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61045

noncomputable section

open Classical
open scoped BigOperators

abbrev BitCube (I : Type*) := I → Bool
abbrev BitHistory (I : Type*) := I → Option Bool

def bitAsSign (b : Bool) : ℝ := if b then 1 else -1

def revealedCoordinates {I : Type*} [Fintype I]
    (h : BitHistory I) : Finset I :=
  Finset.univ.filter (fun i => (h i).isSome)

def unrevealedCoordinates {I : Type*} [Fintype I]
    (h : BitHistory I) : Finset I :=
  Finset.univ \ revealedCoordinates h

def compatibleHistory {I : Type*}
    (h : BitHistory I) (x : BitCube I) : Prop :=
  ∀ i b, h i = some b → x i = b

def historyMass {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (h : BitHistory I) : ℝ :=
  ∑ x : BitCube I, if compatibleHistory h x then mass x else 0

def conditionalMean {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  if historyMass mass h = 0 then 0 else
    (∑ x : BitCube I,
      if compatibleHistory h x then mass x * f x else 0) / historyMass mass h

def conditionalVariance {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  if historyMass mass h = 0 then 0 else
    (∑ x : BitCube I,
      if compatibleHistory h x then
        mass x * (f x - conditionalMean mass f h) ^ 2
      else 0) / historyMass mass h

def measurableOnHistory {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : Prop :=
  ∀ x y,
    compatibleHistory h x → compatibleHistory h y →
    0 < mass x → 0 < mass y → f x = f y

def posteriorMean {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  conditionalMean mass f h

def posteriorVariance {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  conditionalVariance mass f h

def observeHistory {I : Type*}
    (h : BitHistory I) (x : BitCube I) (i : I) : BitHistory I :=
  Function.update h i (some (x i))

def historyAtFrom {I : Type*}
    (policy : BitHistory I → Option I) (h : BitHistory I)
    (x : BitCube I) : ℕ → BitHistory I
  | 0 => h
  | t + 1 =>
      let h' := historyAtFrom policy h x t
      match policy h' with
      | none => h'
      | some i => observeHistory h' x i

def conditionalAverage {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (h : BitHistory I)
    (g : BitCube I → ℝ) : ℝ :=
  if historyMass mass h = 0 then 0 else
    (∑ x : BitCube I,
      if compatibleHistory h x then mass x * g x else 0) / historyMass mass h

def policyRiskFrom {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) (policy : BitHistory I → Option I) : ℝ :=
  ∑' t : ℕ,
    conditionalAverage mass h
      (fun x =>
        if (policy (historyAtFrom policy h x t)).isSome then
          posteriorVariance mass f (historyAtFrom policy h x t)
        else 0)

def admissiblePolicy {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) (policy : BitHistory I → Option I) : Prop :=
  (∀ h' i, policy h' = some i → h' i = none) ∧
  (∀ x, compatibleHistory h x → 0 < mass x → ∃ t,
    measurableOnHistory mass f (historyAtFrom policy h x t))

def optimalRisk {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (f : BitCube I → ℝ)
    (h : BitHistory I) : ℝ :=
  sInf {r : ℝ |
    ∃ policy : BitHistory I → Option I,
      admissiblePolicy mass f h policy ∧
      r = policyRiskFrom mass f h policy}

def finiteMinimum {I : Type*} [Fintype I]
    (s : Finset I) (g : I → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ i, i ∈ s ∧ r = g i}

def uniformMass {I : Type*} [Fintype I] (_ : BitCube I) : ℝ :=
  1 / (2 : ℝ) ^ Fintype.card I

def emptyHistory {I : Type*} : BitHistory I := fun _ => none

inductive BooleanDecisionTree (I : Type*) where
  | leaf : Bool → BooleanDecisionTree I
  | query : I → BooleanDecisionTree I → BooleanDecisionTree I →
      BooleanDecisionTree I

def BooleanDecisionTree.evaluate {I : Type*} :
    BooleanDecisionTree I → BitCube I → Bool
  | .leaf b, _ => b
  | .query i left right, x =>
      if x i then evaluate right x else evaluate left x

def BooleanDecisionTree.depth {I : Type*} :
    BooleanDecisionTree I → ℕ
  | .leaf _ => 0
  | .query _ left right => 1 + max left.depth right.depth

def treeValue {I : Type*}
    (tree : BooleanDecisionTree I) (x : BitCube I) : ℝ :=
  bitAsSign (tree.evaluate x)

def freshTreeQuery {I : Type*} :
    BooleanDecisionTree I → BitHistory I → Option I
  | .leaf _, _ => none
  | .query i left right, h =>
      if h i = none then some i else
        match h i with
        | some true => freshTreeQuery right h
        | some false => freshTreeQuery left h
        | none => some i

def treeUsesOnlyFrom {I : Type*}
    (block : Finset I) : BooleanDecisionTree I → Prop
  | .leaf _ => True
  | .query i left right =>
      i ∈ block ∧ treeUsesOnlyFrom block left ∧ treeUsesOnlyFrom block right

def treeUsesOnly {I : Type*}
    (block : Finset I) (tree : BooleanDecisionTree I) : Prop :=
  treeUsesOnlyFrom block tree

def treeHasFreshQuery {I : Type*}
    (tree : BooleanDecisionTree I) (h : BitHistory I) : Prop :=
  (freshTreeQuery tree h).isSome

def sequentialComponentPolicy {I : Type*} [Fintype I] {m : ℕ}
    (trees : Fin m → BooleanDecisionTree I) :
    BitHistory I → Option I :=
  fun h =>
    ((Finset.univ.filter (fun j : Fin m =>
      treeHasFreshQuery (trees j) h)).toList.head?).bind
      (fun j => freshTreeQuery (trees j) h)

def orderedWeights {m : ℕ} (weights : Fin m → ℝ) : Prop :=
  ∀ r s, r.val < s.val → weights s ≤ weights r

def validProbabilityWeights {m : ℕ} (weights : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ weights j) ∧ ∑ j : Fin m, weights j = 1

def pairwiseDisjointBlocks {I : Type*} {m : ℕ}
    (blocks : Fin m → Finset I) : Prop :=
  ∀ r s, r ≠ s → Disjoint (blocks r) (blocks s)

def treeMixtureTarget {I : Type*} {m : ℕ}
    (weights : Fin m → ℝ) (trees : Fin m → BooleanDecisionTree I)
    (x : BitCube I) : ℝ :=
  ∑ j : Fin m, weights j * treeValue (trees j) x

def claim61045 : Prop :=
  ∀ (I : Type*) [Fintype I] (m k : ℕ)
    (blocks : Fin m → Finset I)
    (weights : Fin m → ℝ)
    (trees : Fin m → BooleanDecisionTree I),
    pairwiseDisjointBlocks blocks →
    validProbabilityWeights weights →
    orderedWeights weights →
    (∀ j,
      treeUsesOnly (blocks j) (trees j) ∧
      (trees j).depth ≤ k) →
    let target := treeMixtureTarget weights trees
    let policy := sequentialComponentPolicy trees
    (∀ h,
      (unrevealedCoordinates h).Nonempty →
      optimalRisk uniformMass target h =
        posteriorVariance uniformMass target h +
          finiteMinimum (unrevealedCoordinates h)
            (fun i => conditionalAverage uniformMass h
              (fun x => optimalRisk uniformMass target
                (observeHistory h x i)))) ∧
    policyRiskFrom uniformMass target (emptyHistory) policy ≤
      (k : ℝ) * ∑ r : Fin m,
        ((r.val : ℝ) + 1) * (weights r) ^ 2 ∧
    (k : ℝ) * ∑ r : Fin m,
        ((r.val : ℝ) + 1) * (weights r) ^ 2 ≤ (k : ℝ) ∧
    (∀ h,
      policy h ≠ none →
      posteriorVariance uniformMass target h +
        finiteMinimum (unrevealedCoordinates h)
          (fun i => conditionalAverage uniformMass h
            (fun x => policyRiskFrom uniformMass target
              (observeHistory h x i) policy)) ≤
        policyRiskFrom uniformMass target h policy)

end
end MathlibPlus.Open.ResearchFormalization.Claim61045
