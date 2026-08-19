import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim61051

noncomputable section

open Classical
open scoped BigOperators

abbrev BitCube (I : Type*) := I → Bool
abbrev BitHistory (I : Type*) := I → Option Bool

def bitAsReal (b : Bool) : ℝ := if b then 1 else 0

def revealedCoordinates {I : Type*} [Fintype I]
    (h : BitHistory I) : Finset I :=
  Finset.univ.filter (fun i => (h i).isSome)

def compatibleHistory {I : Type*}
    (h : BitHistory I) (x : BitCube I) : Prop :=
  ∀ i b, h i = some b → x i = b

def bernoulliMass {I : Type*} [Fintype I]
    (parameters : I → ℝ) (x : BitCube I) : ℝ :=
  ∏ i : I, if x i then parameters i else 1 - parameters i

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

def emptyHistory {I : Type*} : BitHistory I := fun _ => none

inductive PrefixTree (I : Type*) where
  | leaf : PrefixTree I
  | query : I → PrefixTree I → PrefixTree I → PrefixTree I

def PrefixTree.depth {I : Type*} : PrefixTree I → ℕ
  | .leaf => 0
  | .query _ left right => 1 + max left.depth right.depth

def PrefixTree.noRepeatFrom {I : Type*}
    (seen : Finset I) : PrefixTree I → Prop
  | .leaf => True
  | .query i left right =>
      i ∉ seen ∧ noRepeatFrom (insert i seen) left ∧
        noRepeatFrom (insert i seen) right

def PrefixTree.noRepeat {I : Type*} (P : PrefixTree I) : Prop :=
  P.noRepeatFrom ∅

def PrefixTree.follows {I : Type*} :
    PrefixTree I → BitCube I → List Bool → Prop
  | _, _, [] => True
  | .leaf, _, _ :: _ => False
  | .query i left right, x, b :: path =>
      if x i = b then
        if b then follows right x path else follows left x path
      else False

def PrefixTree.leafPaths {I : Type*} : PrefixTree I → Finset (List Bool)
  | .leaf => {[]}
  | .query _ left right =>
      (leafPaths left).image (fun p => false :: p) ∪
        (leafPaths right).image (fun p => true :: p)

def PrefixTree.queryCoordinates {I : Type*} :
    PrefixTree I → List Bool → Finset I
  | .leaf, _ => ∅
  | .query i _left _right, [] => {i}
  | .query i left right, b :: path =>
      insert i (if b then queryCoordinates right path
        else queryCoordinates left path)

def PrefixTree.freshQuery {I : Type*} :
    PrefixTree I → BitHistory I → Option I
  | .leaf, _ => none
  | .query i left right, h =>
      if h i = none then some i else
        match h i with
        | some true => freshQuery right h
        | some false => freshQuery left h
        | none => some i

def PrefixTree.reachedPath {I : Type*} :
    PrefixTree I → BitHistory I → List Bool
  | .leaf, _ => []
  | .query i left right, h =>
      match h i with
      | none => []
      | some true => true :: reachedPath right h
      | some false => false :: reachedPath left h

def PrefixTree.unrevealedAtPath {I : Type*} [Fintype I]
    (P : PrefixTree I) (path : List Bool) : Finset I :=
  Finset.univ \ P.queryCoordinates path

inductive OneQueryTree (I : Type*) where
  | leaf : ℝ → OneQueryTree I
  | query : I → OneQueryTree I → OneQueryTree I → OneQueryTree I

def OneQueryTree.evaluate {I : Type*} :
    OneQueryTree I → BitCube I → ℝ
  | .leaf v, _ => v
  | .query i left right, x =>
      if x i then evaluate right x else evaluate left x

def OneQueryTree.depth {I : Type*} : OneQueryTree I → ℕ
  | .leaf _ => 0
  | .query _ left right => 1 + max left.depth right.depth

def OneQueryTree.queryCoordinates {I : Type*} :
    OneQueryTree I → Finset I
  | .leaf _ => ∅
  | .query i left right => insert i (left.queryCoordinates ∪ right.queryCoordinates)

def OneQueryTree.affineIntercept {I : Type*} :
    OneQueryTree I → ℝ
  | .leaf v => v
  | .query _ left _right => left.affineIntercept

def OneQueryTree.affineCoefficient {I : Type*}
    (j : I) : OneQueryTree I → ℝ
  | .leaf _ => 0
  | .query i left right =>
      if i = j then right.affineIntercept - left.affineIntercept else 0

def residualIntercept {I : Type*} {N : ℕ}
    (weights : Fin N → ℝ) (trees : Fin N → OneQueryTree I) : ℝ :=
  ∑ i : Fin N, weights i * (trees i).affineIntercept

def residualCoefficient {I : Type*} {N : ℕ}
    (weights : Fin N → ℝ) (trees : Fin N → OneQueryTree I)
    (j : I) : ℝ :=
  ∑ i : Fin N, weights i * (trees i).affineCoefficient j

def validResidualTrees {I : Type*} [Fintype I] {N : ℕ}
    (_weights : Fin N → ℝ) (f : Fin N → BitCube I → ℝ)
    (P : PrefixTree I)
    (residuals : List Bool → Fin N → OneQueryTree I) : Prop :=
  ∀ path ∈ P.leafPaths,
    (∀ i, (residuals path i).depth ≤ 1 ∧
      (residuals path i).queryCoordinates ⊆
        P.unrevealedAtPath path ∧
      (∀ x, P.follows x path →
        f i x = (residuals path i).evaluate x))

def residualRepresentation {I : Type*} [Fintype I] {N : ℕ}
    (weights : Fin N → ℝ) (f : Fin N → BitCube I → ℝ)
    (P : PrefixTree I)
    (residuals : List Bool → Fin N → OneQueryTree I)
    (path : List Bool) : Prop :=
  path ∈ P.leafPaths →
    ∀ x, P.follows x path →
      (∑ i : Fin N, weights i * f i x) =
        residualIntercept weights (residuals path) +
          ∑ j : I,
            residualCoefficient weights (residuals path) j * bitAsReal (x j)

def residualOrder {I : Type*} [Fintype I] {N : ℕ}
    (weights : Fin N → ℝ)
    (residuals : List Bool → Fin N → OneQueryTree I)
    (path : List Bool) (order : List I) : Prop :=
  order.Nodup ∧
    (∀ j, residualCoefficient weights (residuals path) j ≠ 0 ↔
      j ∈ order) ∧
    order.Pairwise (fun i j =>
      |residualCoefficient weights (residuals path) j| ≤
        |residualCoefficient weights (residuals path) i|)

def commonPrefixResidualPolicy {I : Type*} [Fintype I]
    (parameters : I → ℝ)
    (mass : BitCube I → ℝ) (target : BitCube I → ℝ)
    (P : PrefixTree I)
    (orders : List Bool → List I) : BitHistory I → Option I :=
  fun h =>
    match P.freshQuery h with
    | some i => some i
    | none =>
        if measurableOnHistory mass target h then none else
          (orders (P.reachedPath h)).find? (fun i =>
            h i = none ∧ 0 < parameters i ∧ parameters i < 1)

def posteriorMeanEstimateAfterFreshReveal {I : Type*} [Fintype I]
    (mass : BitCube I → ℝ) (target : BitCube I → ℝ)
    (policy : BitHistory I → Option I)
    (h : BitHistory I) (x : BitCube I) (t : ℕ) : ℝ :=
  match policy (historyAtFrom policy h x t) with
  | none => posteriorMean mass target (historyAtFrom policy h x t)
  | some i =>
      posteriorMean mass target
        (observeHistory (historyAtFrom policy h x t) x i)

def claim61051 : Prop :=
  ∀ (I : Type*) [Fintype I] (N k r : ℕ)
    (parameters : I → ℝ)
    (weights : Fin N → ℝ)
    (f : Fin N → BitCube I → ℝ)
    (P : PrefixTree I),
    (∀ i, 0 ≤ parameters i ∧ parameters i ≤ 1) →
    (∀ i, 0 ≤ weights i) →
    ∑ i : Fin N, weights i = 1 →
    (∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) →
    r + 1 ≤ k →
    P.depth ≤ r →
    (∃ residuals : List Bool → Fin N → OneQueryTree I,
      validResidualTrees weights f P residuals) →
    ∃ residuals : List Bool → Fin N → OneQueryTree I,
      ∃ orders : List Bool → List I,
        validResidualTrees weights f P residuals ∧
        (∀ path, residualRepresentation weights f P residuals path) ∧
        (∀ path ∈ P.leafPaths,
          residualOrder weights residuals path (orders path)) ∧
        let mass := bernoulliMass parameters
        let target := fun x => ∑ i : Fin N, weights i * f i x
        let policy := commonPrefixResidualPolicy
          parameters mass target P orders
        admissiblePolicy mass target (emptyHistory) policy ∧
        (∀ h, policy h = none → measurableOnHistory mass target h) ∧
        (∃ estimates : BitCube I → ℕ → ℝ,
          ∀ x t i,
            policy (historyAtFrom policy (emptyHistory) x t) = some i →
              estimates x t =
                posteriorMean mass target
                  (observeHistory
                    (historyAtFrom policy (emptyHistory) x t) x i)) ∧
        policyRiskFrom mass target (emptyHistory) policy ≤
          ((r + 1 : ℕ) : ℝ) / 4 ∧
        ((r + 1 : ℕ) : ℝ) / 4 ≤ (k : ℝ) / 4 ∧
        (k : ℝ) / 4 ≤ (k : ℝ) ∧
        (∀ path ∈ P.leafPaths, ∀ x, P.follows x path →
          target x =
            residualIntercept weights (residuals path) +
              ∑ j : I,
                residualCoefficient weights (residuals path) j *
                  bitAsReal (x j))

end
end MathlibPlus.Open.ResearchFormalization.Claim61051
