import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

inductive Sign where
  | neg
  | pos
  deriving DecidableEq

namespace Sign

def toReal : Sign → ℝ
  | .neg => -1
  | .pos => 1

end Sign

abbrev Oracle (I : Type*) := I → Sign

inductive DecisionTree (I : Type*) (Y : Type*) where
  | leaf : Y → DecisionTree I Y
  | query : I → DecisionTree I Y → DecisionTree I Y → DecisionTree I Y

namespace DecisionTree

def eval (tree : DecisionTree I Y) (oracle : Oracle I) : Y :=
  match tree with
  | .leaf value => value
  | .query coordinate negative positive =>
      match oracle coordinate with
      | .neg => eval negative oracle
      | .pos => eval positive oracle

def depth : DecisionTree I Y → ℕ
  | .leaf _ => 0
  | .query _ negative positive => max (depth negative) (depth positive) + 1

def queries (tree : DecisionTree I Y) (oracle : Oracle I) : ℕ :=
  match tree with
  | .leaf _ => 0
  | .query coordinate negative positive =>
      match oracle coordinate with
      | .neg => queries negative oracle + 1
      | .pos => queries positive oracle + 1

def legal [DecidableEq I] : DecisionTree I Y → Finset I → Prop
  | .leaf _, _ => True
  | .query coordinate negative positive, used =>
      coordinate ∉ used ∧
        legal negative (insert coordinate used) ∧
        legal positive (insert coordinate used)

end DecisionTree

def IsProbabilityDistribution [Fintype C] (p : C → ℝ) : Prop :=
  (∀ c, 0 ≤ p c) ∧ ∑ c : C, p c = 1

def componentValue (M : C → Oracle I → Sign) (c : C) (oracle : Oracle I) : ℝ :=
  (M c oracle).toReal

def queryCount (trees : C → DecisionTree I Sign) (c : C) (oracle : Oracle I) : ℕ :=
  (trees c).queries oracle

def fullMean [Fintype C] (p : C → ℝ) (M : C → Oracle I → Sign)
    (oracle : Oracle I) : ℝ :=
  ∑ c : C, p c * componentValue M c oracle

def truncatedMean [Fintype C] (p : C → ℝ) (M : C → Oracle I → Sign)
    (trees : C → DecisionTree I Sign) (oracle : Oracle I) (m : ℕ) : ℝ :=
  Finset.sum (Finset.univ.filter (fun c => queryCount trees c oracle ≤ m))
    (fun c => p c * componentValue M c oracle)

def residual [Fintype C] (p : C → ℝ) (M : C → Oracle I → Sign)
    (trees : C → DecisionTree I Sign) (oracle : Oracle I) (m : ℕ) : ℝ :=
  |fullMean p M oracle - truncatedMean p M trees oracle m|

def tailProbability [Fintype C] (p : C → ℝ)
    (trees : C → DecisionTree I Sign) (oracle : Oracle I) (m : ℕ) : ℝ :=
  Finset.sum (Finset.univ.filter (fun c => m < queryCount trees c oracle)) (fun c => p c)

def pairCollisionExpectation [Fintype C] (p : C → ℝ)
    (trees : C → DecisionTree I Sign) (oracle : Oracle I) : ℝ :=
  ∑ x : C, ∑ y : C,
    p x * p y * ((min (queryCount trees x oracle) (queryCount trees y oracle) : ℕ) : ℝ)

def expectedCommunication [Fintype C] (p : C → ℝ)
    (trees : C → DecisionTree I Sign) (oracle : Oracle I) : ℝ :=
  ∑ x : C, p x * ((queryCount trees x oracle : ℕ) : ℝ)

def oracleAreaSignMatrixPairCollision : Prop :=
  ∀ {I C : Type*} [Fintype I] [Fintype C] [DecidableEq I]
    (k : ℕ) (M : C → Oracle I → Sign) (p : C → ℝ)
    (trees : C → DecisionTree I Sign) (oracle : Oracle I),
    IsProbabilityDistribution p ∧
      (∀ c, DecisionTree.legal (trees c) ∅) ∧
      (∀ c, DecisionTree.depth (trees c) ≤ k) ∧
      (∀ c ω, DecisionTree.eval (trees c) ω = M c ω) →
    (Finset.sum (Finset.range k) (fun m => (residual p M trees oracle m) ^ 2)) ≤
        Finset.sum (Finset.range k) (fun m => (tailProbability p trees oracle m) ^ 2) ∧
      (Finset.sum (Finset.range k) (fun m => (tailProbability p trees oracle m) ^ 2)) =
        pairCollisionExpectation p trees oracle ∧
      pairCollisionExpectation p trees oracle ≤ expectedCommunication p trees oracle ∧
      expectedCommunication p trees oracle ≤ (k : ℝ)

end MathlibPlus.Open.Analysis
