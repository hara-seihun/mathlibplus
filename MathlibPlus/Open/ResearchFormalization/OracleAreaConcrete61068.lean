import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaConcrete61068

open Classical
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable section

abbrev Sign := Bool
abbrev Coordinate := Fin 4
abbrev State := Coordinate → Sign
abbrev Transcript := Coordinate → Option Sign

def signValue : Sign → ℝ
  | false => -1
  | true => 1

def stateSpace : Finset State := Finset.univ

def uniformAverage (f : State → ℝ) : ℝ :=
  (∑ ω : State, f ω) / (Fintype.card State : ℝ)

def treeTarget (ω : State) (a b : Coordinate) : ℝ :=
  signValue (ω a) * signValue (ω b)

def T₁ (ω : State) : ℝ := treeTarget ω 0 1

def T₂ (ω : State) : ℝ := treeTarget ω 0 2

def T₃ (ω : State) : ℝ := treeTarget ω 0 3

def mixtureTarget (ω : State) : ℝ :=
  (T₁ ω + T₂ ω + T₃ ω) / 3

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

def DecisionTree.queryCoordinates [DecidableEq ι]
    : DecisionTree ι → Finset ι
  | .leaf _ => ∅
  | .query coordinate negative positive =>
      insert coordinate (negative.queryCoordinates ∪ positive.queryCoordinates)

def productTree (a b : Coordinate) : DecisionTree Coordinate :=
  .query a
    (.query b (.leaf true) (.leaf false))
    (.query b (.leaf false) (.leaf true))

def tree₁ : DecisionTree Coordinate := productTree 0 1
def tree₂ : DecisionTree Coordinate := productTree 0 2
def tree₃ : DecisionTree Coordinate := productTree 0 3

def residualLabelsAfterRoot : DecisionTree Coordinate → Finset Coordinate
  | .leaf _ => ∅
  | .query _ negative positive =>
      negative.queryCoordinates ∪ positive.queryCoordinates

def emptyTranscript : Transcript := fun _ => none

def observe (h : Transcript) (c : Coordinate) (s : Sign) : Transcript :=
  Function.update h c (some s)

def transcriptA (ω : State) : Transcript :=
  observe emptyTranscript 0 (ω 0)

def transcriptAB (ω : State) : Transcript :=
  observe (transcriptA ω) 1 (ω 1)

def transcriptABC (ω : State) : Transcript :=
  observe (transcriptAB ω) 2 (ω 2)

def transcriptABCD (ω : State) : Transcript :=
  observe (transcriptABC ω) 3 (ω 3)

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

def fixedPolicyOrder : Fin 4 → Coordinate := fun i => i

def targetMeasurable (h : Transcript) : Prop :=
  ∀ ω₁ ∈ compatibleStates h, ∀ ω₂ ∈ compatibleStates h,
    mixtureTarget ω₁ = mixtureTarget ω₂

def fixedTranscript (ω : State) (m : Fin 5) : Transcript :=
  match m.1 with
  | 0 => emptyTranscript
  | 1 => transcriptA ω
  | 2 => transcriptAB ω
  | 3 => transcriptABC ω
  | _ => transcriptABCD ω

def fixedPolicyLegal : Prop :=
  Function.Injective fixedPolicyOrder ∧
    ∀ (m : Fin 4) (ω : State),
      (fixedTranscript ω (Fin.castSucc m)) (fixedPolicyOrder m) = none ∧
      ¬targetMeasurable (fixedTranscript ω (Fin.castSucc m))

noncomputable def expectedPosteriorVariance (m : Fin 5) : ℝ :=
  (∑ ω : State, posteriorVariance (fixedTranscript ω m)) /
    (Fintype.card State : ℝ)

noncomputable def fixedPolicyArea : ℝ :=
  ∑ m : Fin 5, expectedPosteriorVariance m

/-- Claim 61068: the fixed mixture of the three common-root product trees has
pairwise-disjoint residual coordinates after the root reveal, and the actual
fixed policy has the stated expected posterior-variance sequence and area. -/
def claim61068 : Prop :=
  stateSpace.card = 16 ∧
    fixedPolicyLegal ∧
    tree₁.depth = 2 ∧
    tree₂.depth = 2 ∧
    tree₃.depth = 2 ∧
    tree₁.queryCoordinates = {0, 1} ∧
    tree₂.queryCoordinates = {0, 2} ∧
    tree₃.queryCoordinates = {0, 3} ∧
    residualLabelsAfterRoot tree₁ = {1} ∧
    residualLabelsAfterRoot tree₂ = {2} ∧
    residualLabelsAfterRoot tree₃ = {3} ∧
    Disjoint (residualLabelsAfterRoot tree₁)
      (residualLabelsAfterRoot tree₂) ∧
    Disjoint (residualLabelsAfterRoot tree₁)
      (residualLabelsAfterRoot tree₃) ∧
    Disjoint (residualLabelsAfterRoot tree₂)
      (residualLabelsAfterRoot tree₃) ∧
    (∀ ω : State,
      signValue (tree₁.evaluate ω) = T₁ ω ∧
        signValue (tree₂.evaluate ω) = T₂ ω ∧
        signValue (tree₃.evaluate ω) = T₃ ω ∧
        mixtureTarget ω =
          signValue (ω 0) *
            (signValue (ω 1) + signValue (ω 2) + signValue (ω 3)) / 3) ∧
    expectedPosteriorVariance 0 = 1 / 3 ∧
    expectedPosteriorVariance 1 = 1 / 3 ∧
    expectedPosteriorVariance 2 = 2 / 9 ∧
    expectedPosteriorVariance 3 = 1 / 9 ∧
    expectedPosteriorVariance 4 = 0 ∧
    fixedPolicyArea = 1 ∧
    fixedPolicyArea < 2

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaConcrete61068
