import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

noncomputable section

universe u v w

/-- Finite binary decision trees whose internal nodes query a bit coordinate. -/
inductive BinaryQueryTree (k : Nat) (Action : Type u) where
  | leaf : Action → BinaryQueryTree k Action
  | query : Fin k → BinaryQueryTree k Action → BinaryQueryTree k Action →
      BinaryQueryTree k Action

def BinaryQueryTree.run {k : Nat} {Action : Type u} :
    BinaryQueryTree k Action → (Fin k → Bool) → Action
  | .leaf action, _ => action
  | .query coordinate onTrue onFalse, oracle =>
      match oracle coordinate with
      | true => BinaryQueryTree.run onTrue oracle
      | false => BinaryQueryTree.run onFalse oracle

def BinaryQueryTree.height {k : Nat} {Action : Type u} :
    BinaryQueryTree k Action → Nat
  | .leaf _ => 0
  | .query _ onTrue onFalse =>
      1 + max (BinaryQueryTree.height onTrue) (BinaryQueryTree.height onFalse)

def BinaryQueryTree.queryTrace {k : Nat} {Action : Type u} :
    BinaryQueryTree k Action → (Fin k → Bool) → List (Fin k)
  | .leaf _, _ => []
  | .query coordinate onTrue onFalse, oracle =>
      coordinate ::
        match oracle coordinate with
        | true => BinaryQueryTree.queryTrace onTrue oracle
        | false => BinaryQueryTree.queryTrace onFalse oracle

/-- Every path queries the coordinates exactly once in the displayed common order. -/
def BinaryQueryTree.queriesOnceInCommonOrder
    {k : Nat} {Action : Type u} (tree : BinaryQueryTree k Action) : Prop :=
  ∀ oracle, BinaryQueryTree.queryTrace tree oracle = List.ofFn (fun i : Fin k => i)

def IsFiniteDistribution {Oracle : Type v} [Fintype Oracle]
    (mass : Oracle → ℝ) : Prop :=
  (∀ oracle, 0 ≤ mass oracle) ∧ ∑ oracle, mass oracle = 1

def expectedReward {Action : Type u} {Oracle : Type v} [Fintype Oracle]
    (mass : Oracle → ℝ) (action : Oracle → Action)
    (reward : Action → Oracle → ℝ) : ℝ :=
  ∑ oracle, mass oracle * reward (action oracle) oracle

/-- Exact fixed-level policy replacement, reward preservation, and the sharp bound. -/
def binaryQueryTreeReplacementClaim : Prop :=
  ∀ (k : Nat) (Action : Type u) (Component : Type v)
    (policy : Component → (Fin k → Bool) → Action),
    ∃ trees : Component → BinaryQueryTree k Action,
      (∀ component, BinaryQueryTree.height (trees component) ≤ k) ∧
      (∀ component,
        BinaryQueryTree.queriesOnceInCommonOrder (trees component)) ∧
      (∀ component oracle,
        BinaryQueryTree.run (trees component) oracle = policy component oracle) ∧
      (∀ (Reward : Type w) (reward : Action → (Fin k → Bool) → Reward)
          component oracle,
        reward (BinaryQueryTree.run (trees component) oracle) oracle =
          reward (policy component oracle) oracle) ∧
      (∀ (reward : Action → (Fin k → Bool) → ℝ) (mass : (Fin k → Bool) → ℝ)
          (_hMass : IsFiniteDistribution mass) component,
        expectedReward mass (fun oracle =>
            BinaryQueryTree.run (trees component) oracle) reward =
          expectedReward mass (policy component) reward) ∧
      (∀ tree : BinaryQueryTree k (Fin k → Bool),
        (∀ oracle, BinaryQueryTree.run tree oracle = oracle) →
          k ≤ BinaryQueryTree.height tree)

end
end MathlibPlus.Open.Research
