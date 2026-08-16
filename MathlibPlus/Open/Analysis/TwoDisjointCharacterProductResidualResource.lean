import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open

abbrev Sign := Bool
abbrev SignedConfiguration (I : Type*) := I → Sign

/-- The numerical value of a sign in the two-point cube. -/
def signValue (x : Sign) : ℝ := if x then 1 else -1

/-- Expectation under the uniform measure on a finite type. -/
def uniformAverage {α : Type*} [Finite α] (f : α → ℝ) : ℝ :=
  letI : Fintype α := Fintype.ofFinite α
  (Fintype.card α : ℝ)⁻¹ * (Finset.univ.sum f)

def finiteSum {α : Type*} [Finite α] (f : α → ℝ) : ℝ :=
  letI : Fintype α := Fintype.ofFinite α
  Finset.univ.sum f

abbrev Remaining (I : Type*) [DecidableEq I] (D : Finset I) := {i : I // i ∉ D}
abbrev RemainingConfiguration (I : Type*) [DecidableEq I] (D : Finset I) :=
  Remaining I D → Sign

/-- Extend a partial sign transcript by a configuration on the unrevealed coordinates. -/
def extendTranscript {I : Type*} [DecidableEq I] {D : Finset I}
    (h : I → Sign) (y : RemainingConfiguration I D) : SignedConfiguration I :=
  fun i => if hi : i ∈ D then h i else y ⟨i, hi⟩

/-- The Fourier character indexed by a finite set of coordinates. -/
def signCharacter {α : Type*} (A : Finset α) (x : α → Sign) : ℝ :=
  A.prod (fun i => signValue (x i))

/-- The density in the two-disjoint-character family. -/
def twoCharacterDensity {I : Type*} [DecidableEq I]
    (S T : Finset I) (a b : ℝ) (x : SignedConfiguration I) : ℝ :=
  (1 + a * signCharacter S x) * (1 + b * signCharacter T x)

/-- Uniform product mass on the finite sign cube. -/
def uniformProductMass {I : Type*} [Fintype I]
    (x : SignedConfiguration I) : ℝ :=
  letI : Fintype (SignedConfiguration I) := Fintype.ofFinite _
  (Fintype.card (SignedConfiguration I) : ℝ)⁻¹

/-- The mass obtained by multiplying the uniform product mass by a density. -/
def densityMass {I : Type*} [Fintype I]
    (q : SignedConfiguration I → ℝ) (x : SignedConfiguration I) : ℝ :=
  uniformProductMass x * q x

/-- Probability of a reveal transcript under the density relative to uniform product measure. -/
def transcriptProbability {I : Type*} [Fintype I] [DecidableEq I]
    (q : SignedConfiguration I → ℝ) (D : Finset I) (h : I → Sign) : ℝ :=
  uniformAverage (fun x => if (∀ i ∈ D, x i = h i) then q x else 0)

/-- Conditional density on the still-unrevealed cube. -/
def transcriptMass {I : Type*} [Fintype I] [DecidableEq I]
    (q : SignedConfiguration I → ℝ) (D : Finset I) (h : I → Sign) : ℝ :=
  uniformAverage (fun y : RemainingConfiguration I D => q (extendTranscript h y))

def posteriorDensity {I : Type*} [Fintype I] [DecidableEq I]
    (q : SignedConfiguration I → ℝ) (D : Finset I) (h : I → Sign)
    (y : RemainingConfiguration I D) : ℝ :=
  q (extendTranscript h y) / transcriptMass q D h

def posteriorResidual {I : Type*} [Fintype I] [DecidableEq I]
    (q : SignedConfiguration I → ℝ) (D : Finset I) (h : I → Sign) :
    RemainingConfiguration I D → ℝ :=
  fun y => posteriorDensity q D h y - 1

/-- The coordinates of a character which remain after a transcript. -/
def activeCoordinates {I : Type*} [Fintype I] [DecidableEq I]
    (A D : Finset I) : Finset (Remaining I D) :=
  letI : Fintype (Remaining I D) := Fintype.ofFinite _
  Finset.univ.filter (fun i => (i : I) ∈ A)

def revealedCharacter {I : Type*} [DecidableEq I]
    (A D : Finset I) (h : I → Sign) : ℝ :=
  (A.filter (fun i => i ∈ D)).prod (fun i => signValue (h i))

def activeAmplitude {I : Type*} [DecidableEq I]
    (A : Finset I) (c : ℝ) (D : Finset I) (h : I → Sign) : ℝ :=
  if A ⊆ D then 0 else c * revealedCharacter A D h

/-- The exact two active character factors of a posterior density. -/
def posteriorHasTwoActiveFactors {I : Type*} [Fintype I] [DecidableEq I]
    (q : SignedConfiguration I → ℝ) (S T : Finset I) (a b : ℝ)
    (D : Finset I) (h : I → Sign) : Prop :=
  ∀ y : RemainingConfiguration I D,
    posteriorDensity q D h y =
      (1 + activeAmplitude S a D h * signCharacter (activeCoordinates S D) y) *
        (1 + activeAmplitude T b D h * signCharacter (activeCoordinates T D) y)

def fourierCoefficient {I : Type*} [Fintype I] [DecidableEq I]
    {D : Finset I} (g : RemainingConfiguration I D → ℝ)
    (R : Finset (Remaining I D)) : ℝ :=
  uniformAverage (fun y => g y * signCharacter R y)

def residualResource {I : Type*} [Fintype I] [DecidableEq I]
    {D : Finset I} (g : RemainingConfiguration I D → ℝ) : ℝ :=
  finiteSum (fun R : Finset (Remaining I D) =>
    (R.card : ℝ) * (fourierCoefficient g R) ^ 2)

def uniformVariance {I : Type*} [Fintype I] [DecidableEq I]
    {D : Finset I} (g : RemainingConfiguration I D → ℝ) : ℝ :=
  uniformAverage (fun y => (g y - uniformAverage g) ^ 2)

/-- A product probability mass used at a leaf of a decision-tree mixture. -/
def productMass {I : Type*} [Fintype I]
    (p : I → Sign → ℝ) (x : SignedConfiguration I) : ℝ :=
  (Finset.univ.prod (fun i : I => p i (x i)))

/-- A binary decision tree whose leaves carry product probability masses. -/
inductive BinaryDecisionTree (I : Type*) where
  | leaf : ℝ → (I → Sign → ℝ) → BinaryDecisionTree I
  | node : I → BinaryDecisionTree I → BinaryDecisionTree I → BinaryDecisionTree I

def treeDepth {I : Type*} : BinaryDecisionTree I → ℕ
  | .leaf _ _ => 0
  | .node _ left right => max (treeDepth left) (treeDepth right) + 1

def treeWeightSum {I : Type*} : BinaryDecisionTree I → ℝ
  | .leaf weight _ => weight
  | .node _ left right => treeWeightSum left + treeWeightSum right

def treeWeightNonnegative {I : Type*} : BinaryDecisionTree I → Prop
  | .leaf weight _ => 0 ≤ weight
  | .node _ left right => treeWeightNonnegative left ∧ treeWeightNonnegative right

def treeMass {I : Type*} [Fintype I] : BinaryDecisionTree I → SignedConfiguration I → ℝ
  | .leaf weight component, x => weight * productMass component x
  | .node _ left right, x => treeMass left x + treeMass right x

/-- Product and path constraints for every leaf of a decision-tree mixture. -/
def treeLeafProductCondition {I : Type*} [DecidableEq I] :
    BinaryDecisionTree I → (I → Sign) → Finset I → Prop
  | .leaf _ component, path, queried =>
      (∀ i b, 0 ≤ component i b) ∧
        (∀ i, component i false + component i true = 1) ∧
        (∀ i, i ∈ queried →
          component i (path i) = 1 ∧ component i (not (path i)) = 0)
  | .node i left right, path, queried =>
      i ∉ queried ∧
        treeLeafProductCondition left (Function.update path i false) (insert i queried) ∧
        treeLeafProductCondition right (Function.update path i true) (insert i queried)

/-- A decision-tree mixture representation of depth at most `k`. -/
def decisionTreeMixtureRepresentation {I : Type*} [Fintype I] [DecidableEq I]
    (μ : SignedConfiguration I → ℝ) (k : ℕ) : Prop :=
  ∃ tree : BinaryDecisionTree I,
    treeDepth tree ≤ k ∧
      treeWeightNonnegative tree ∧
        treeWeightSum tree = 1 ∧
          treeLeafProductCondition tree (fun _ => false) ∅ ∧
            ∀ x, μ x = treeMass tree x

/-- Coordinates in an active block whose squared amplitude is maximal. -/
def maximalActiveCoordinate {I : Type*} [DecidableEq I]
    (S T : Finset I) (a b : ℝ) (D : Finset I) (h : I → Sign) (i : I) : Prop :=
  i ∈ S ∪ T ∧ i ∉ D ∧
    ((i ∈ S ∧
        (activeAmplitude S a D h) ^ 2 ≥ (activeAmplitude T b D h) ^ 2) ∨
      (i ∈ T ∧
        (activeAmplitude T b D h) ^ 2 ≥ (activeAmplitude S a D h) ^ 2))

/-- Exact open formalization of the two-disjoint-character residual-resource claim. -/
def twoDisjointCharacterProductResidualResource : Prop :=
  ∀ (I : Type*) [Fintype I] [DecidableEq I]
    (S T : Finset I) (a b : ℝ),
    S.Nonempty → T.Nonempty → Disjoint S T →
    -1 ≤ a → a ≤ 1 → -1 ≤ b → b ≤ 1 →
    let k : ℕ := S.card + T.card
    let q : SignedConfiguration I → ℝ := twoCharacterDensity S T a b
    let μ : SignedConfiguration I → ℝ := densityMass q
    decisionTreeMixtureRepresentation μ k ∧
      residualResource (posteriorResidual q (∅ : Finset I) (fun _ => false)) ≤ (2 : ℝ) * k ∧
      (∀ (D : Finset I) (h : I → Sign),
        0 < transcriptProbability q D h →
          posteriorHasTwoActiveFactors q S T a b D h) ∧
      (∀ (D : Finset I) (h : I → Sign),
        0 < transcriptProbability q D h →
          posteriorResidual q D h ≠ (fun _ => 0) →
            (∃ i : I, maximalActiveCoordinate S T a b D h i) ∧
              (∀ i : I, maximalActiveCoordinate S T a b D h i →
                ∀ ε : Sign,
                  0 < transcriptProbability q (insert i D) (Function.update h i ε) →
                    residualResource (posteriorResidual q D h) -
                        residualResource
                          (posteriorResidual q (insert i D) (Function.update h i ε)) ≥
                      (1 / 2 : ℝ) * uniformVariance (posteriorResidual q D h)))

end MathlibPlus.Open
