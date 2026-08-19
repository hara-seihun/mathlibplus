import Mathlib
import MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.Open.ResearchFormalization.ROracleClaims61372_61373

open scoped BigOperators
open Classical

noncomputable section

abbrev SignAssignment (I : Type*) := I → Bool

def signValue (b : Bool) : ℝ :=
  if b then 1 else -1

inductive BooleanDecisionTree (I : Type*) where
  | leaf (value : Bool)
  | node (coordinate : I)
      (negative positive : BooleanDecisionTree I)

def BooleanDecisionTree.evaluate {I : Type*} :
    BooleanDecisionTree I → SignAssignment I → Bool
  | .leaf value, _ => value
  | .node coordinate negative positive, x =>
      if x coordinate then positive.evaluate x else negative.evaluate x

def BooleanDecisionTree.depth {I : Type*} :
    BooleanDecisionTree I → ℕ
  | .leaf _ => 0
  | .node _ negative positive =>
      max negative.depth positive.depth + 1

def treeValue {I : Type*}
    (tree : BooleanDecisionTree I) (x : SignAssignment I) : ℝ :=
  signValue (tree.evaluate x)

inductive AtomKind where
  | constant
  | literal
  | parity
  | corner
  | selector

def atomWeightIndex : AtomKind → Fin 5
  | .constant => 0
  | .literal => 1
  | .parity => 2
  | .corner => 3
  | .selector => 4

/-- Semantic shape predicates for the five reduced depth-two atom types. -/
def atomShape {I : Type*}
    (tree : BooleanDecisionTree I) : AtomKind → Prop
  | .constant =>
      ∃ c : Bool, ∀ x, treeValue tree x = signValue c
  | .literal =>
      ∃ i : I, ∃ c : Bool,
        ∀ x, treeValue tree x = signValue c * signValue (x i)
  | .parity =>
      ∃ i : I, ∃ j : I, ∃ c : Bool,
        i ≠ j ∧
          ∀ x, treeValue tree x =
            signValue c * signValue (x i) * signValue (x j)
  | .corner =>
      (∃ r l : I, ∃ c n p : Bool,
        r ≠ l ∧ n ≠ p ∧
          ∀ x, treeValue tree x =
            if x r then
              (if x l then signValue p else signValue n)
            else signValue c) ∨
      (∃ r l : I, ∃ c n p : Bool,
        r ≠ l ∧ n ≠ p ∧
          ∀ x, treeValue tree x =
            if x r then signValue c
            else (if x l then signValue p else signValue n))
  | .selector =>
      ∃ r i j : I, ∃ n₀ p₀ n₁ p₁ : Bool,
        r ≠ i ∧ r ≠ j ∧ i ≠ j ∧ n₀ ≠ p₀ ∧ n₁ ≠ p₁ ∧
          ∀ x, treeValue tree x =
            if x r then
              (if x j then signValue p₁ else signValue n₁)
            else (if x i then signValue p₀ else signValue n₀)

/-- A deterministic semantic reduction label for a valid reduced atom. -/
def canonicalKind {I : Type*}
    (tree : BooleanDecisionTree I) : AtomKind :=
  if atomShape tree .constant then .constant
  else if atomShape tree .literal then .literal
  else if atomShape tree .parity then .parity
  else if atomShape tree .corner then .corner
  else .selector

abbrev AtomLawEntry (I : Type*) :=
  BooleanDecisionTree I × AtomKind × ℝ
abbrev AtomLaw (I : Type*) := List (AtomLawEntry I)

def lawWeightSum {I : Type*} (Λ : AtomLaw I) : ℝ :=
  Λ.foldr (fun entry r => entry.2.2 + r) 0

def atomLawValid {I : Type*} (Λ : AtomLaw I) : Prop :=
  ∀ entry ∈ Λ,
    (entry.1.depth ≤ 2 ∧
      atomShape entry.1 entry.2.1 ∧
        0 ≤ entry.2.2)

def atomLawProbability {I : Type*} (Λ : AtomLaw I) : Prop :=
  atomLawValid Λ ∧ lawWeightSum Λ = 1

def lawTarget {I : Type*}
    (Λ : AtomLaw I) (x : SignAssignment I) : ℝ :=
  Λ.foldr (fun entry r => entry.2.2 * treeValue entry.1 x + r) 0

def lawMean {I : Type*} [Fintype I]
    (Λ : AtomLaw I) : ℝ :=
  (∑ x : SignAssignment I, lawTarget Λ x) /
    (Fintype.card (SignAssignment I) : ℝ)

def lawVariance {I : Type*} [Fintype I]
    (Λ : AtomLaw I) : ℝ :=
  (∑ x : SignAssignment I,
      (lawTarget Λ x - lawMean Λ) ^ 2) /
    (Fintype.card (SignAssignment I) : ℝ)

def lawPhi {I : Type*}
    (Λ : AtomLaw I) (w : AtomKind → ℝ) : ℝ :=
  Λ.foldr (fun entry r => entry.2.2 * w entry.2.1 + r) 0

def restrictTree {I : Type*}
    (tree : BooleanDecisionTree I) (i : I) (b : Bool) :
    BooleanDecisionTree I :=
  match tree with
  | .leaf value => .leaf value
  | .node j negative positive =>
      if j = i then
        if b then restrictTree positive i b else restrictTree negative i b
      else
        .node j (restrictTree negative i b) (restrictTree positive i b)

def restrictAtomLaw {I : Type*}
    (Λ : AtomLaw I) (i : I) (b : Bool) : AtomLaw I :=
  Λ.map (fun entry =>
    (restrictTree entry.1 i b, canonicalKind (restrictTree entry.1 i b), entry.2.2))

def lawDrop {I : Type*} [Fintype I]
    (Λ : AtomLaw I) (w : AtomKind → ℝ) (i : I) : ℝ :=
  lawPhi Λ w -
    (lawPhi (restrictAtomLaw Λ i true) w +
      lawPhi (restrictAtomLaw Λ i false) w) / 2

def targetNonconstant {I : Type*}
    (Λ : AtomLaw I) : Prop :=
  ∃ x y : SignAssignment I, lawTarget Λ x ≠ lawTarget Λ y

def relevantCoordinate {I : Type*}
    (Λ : AtomLaw I) (i : I) : Prop :=
  ∃ x : SignAssignment I,
    lawTarget Λ (Function.update x i true) ≠
      lawTarget Λ (Function.update x i false)

/-- The fixed-representation atom-type Bellman conditions. -/
def fixedRepresentationCertificate
    (w : AtomKind → ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] (Λ : AtomLaw I),
    atomLawProbability Λ →
      0 ≤ lawPhi Λ w ∧ lawPhi Λ w ≤ 2 ∧
        (targetNonconstant Λ →
          ∃ i : I,
            relevantCoordinate Λ i ∧ lawDrop Λ w i ≥ lawVariance Λ)

def upperCappedCertificate
    (w : AtomKind → ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] (Λ : AtomLaw I),
    atomLawProbability Λ →
      lawPhi Λ w ≤ 2 ∧
        (targetNonconstant Λ →
          ∃ i : I,
            relevantCoordinate Λ i ∧ lawDrop Λ w i ≥ lawVariance Λ)

def forcedAtomWeights (w : AtomKind → ℝ) : Prop :=
  w .constant = 0 ∧
    w .literal = 1 ∧
      w .parity = 2 ∧
        w .selector = 2 ∧
          w .corner ≥ 5 / 4

def selectorRTree : BooleanDecisionTree (Fin 4) :=
  .node 0
    (.node 3 (.leaf false) (.leaf true))
    (.node 2 (.leaf true) (.leaf false))

def selectorSTree : BooleanDecisionTree (Fin 4) :=
  .node 1
    (.node 2 (.leaf true) (.leaf false))
    (.node 3 (.leaf false) (.leaf true))

def twoSelectorLaw : AtomLaw (Fin 4) :=
  [(selectorRTree, .selector, 3 / 7),
    (selectorSTree, .selector, 4 / 7)]

def twoSelectorDropEquations (w : AtomKind → ℝ) : Prop :=
  lawDrop twoSelectorLaw w 0 =
      (3 / 7 : ℝ) * (w .selector - w .literal) ∧
    lawDrop twoSelectorLaw w 1 =
      (4 / 7 : ℝ) * (w .selector - w .literal) ∧
      lawDrop twoSelectorLaw w 2 = w .selector - w .corner ∧
        lawDrop twoSelectorLaw w 3 = w .selector - w .corner

def twoSelectorFacts : Prop :=
  atomLawProbability twoSelectorLaw ∧
    targetNonconstant twoSelectorLaw ∧
      lawVariance twoSelectorLaw = 37 / 49 ∧
        ∀ w : AtomKind → ℝ, twoSelectorDropEquations w

def twoSelectorForcedDropBounds (w : AtomKind → ℝ) : Prop :=
  forcedAtomWeights w →
    twoSelectorDropEquations w ∧
      lawDrop twoSelectorLaw w 0 = 3 / 7 ∧
        lawDrop twoSelectorLaw w 1 = 4 / 7 ∧
          lawDrop twoSelectorLaw w 2 ≤ 3 / 4 ∧
            lawDrop twoSelectorLaw w 3 ≤ 3 / 4 ∧
              (3 / 7 : ℝ) < 37 / 49 ∧
                (4 / 7 : ℝ) < 37 / 49 ∧
                  (3 / 4 : ℝ) < 37 / 49

def constantLaw : AtomLaw (Fin 1) :=
  [(.leaf true, .constant, 1)]

def noNonnegativeCertificate (w : AtomKind → ℝ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (Λ : AtomLaw I),
    atomLawProbability Λ ∧ lawPhi Λ w < 0

def routeArea61372 : Prop :=
  MathlibPlus.Open.Probability.ResearchBatch.optimalArea
      (lawTarget twoSelectorLaw) = 45 / 28 ∧
    MathlibPlus.Open.Probability.ResearchBatch.optimalArea
      (lawTarget twoSelectorLaw) < 2

/-- Claim 61372: fixed atom-type weights cannot provide a nonnegative capped
Bellman supersolution; the one-atom pins and the two-selector obstruction are
retained on the explicit semantic atom-law carrier. -/
def claim61372 : Prop :=
  (¬ ∃ w : AtomKind → ℝ, fixedRepresentationCertificate w) ∧
    (∀ w : AtomKind → ℝ,
      fixedRepresentationCertificate w →
        forcedAtomWeights w ∧ twoSelectorForcedDropBounds w) ∧
      twoSelectorFacts ∧ routeArea61372

/-- Claim 61373: after dropping nonnegativity, the displayed weight vector is a
capped Bellman supersolution, and its negative constant-atom value witnesses
that nonnegativity is an independent hypothesis. -/
def claim61373 : Prop :=
  let w : AtomKind → ℝ := fun k =>
    match k with
    | .constant => -2
    | .literal => 0
    | .parity => 2
    | .corner => 1 / 2
    | .selector => 2
  upperCappedCertificate w ∧
    noNonnegativeCertificate w ∧
      lawPhi constantLaw w = -2 ∧
        routeArea61372

end
end MathlibPlus.Open.ResearchFormalization.ROracleClaims61372_61373
