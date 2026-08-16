import Mathlib

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace MathlibPlus.Open.SharpBoundK2

inductive TwoLevelDecisionTree (I : Type u) (S : I → Type v) where
  | leaf : ℝ → TwoLevelDecisionTree I S
  | query : Fin 2 → (i : I) → (S i → TwoLevelDecisionTree I S) → TwoLevelDecisionTree I S

namespace TwoLevelDecisionTree

def eval {I : Type u} {S : I → Type v} :
    TwoLevelDecisionTree I S → ((i : I) → S i) → ℝ
  | .leaf v, _ => v
  | .query _ i next, x => eval (next (x i)) x

def leveledFrom {I : Type u} {S : I → Type v} :
    ℕ → TwoLevelDecisionTree I S → Prop
  | _, .leaf _ => True
  | previous, .query level _ next =>
      previous < level.val + 1 ∧
        ∀ s, leveledFrom (level.val + 1) (next s)

def alignedWith {I : Type u} {S : I → Type v}
    (ell : I → Fin 2) : TwoLevelDecisionTree I S → Prop
  | .leaf _ => True
  | .query level i next =>
      ell i = level ∧ ∀ s, alignedWith ell (next s)

def levelOneAt {I : Type u} {S : I → Type v}
    (q : I) : TwoLevelDecisionTree I S → Prop
  | .leaf _ => True
  | .query level i next =>
      (level ≠ 0 ∨ i = q) ∧ ∀ s, levelOneAt q (next s)

def leavesIn {I : Type u} {S : I → Type v}
    (a b : ℝ) : TwoLevelDecisionTree I S → Prop
  | .leaf v => a ≤ v ∧ v ≤ b
  | .query _ _ next => ∀ s, leavesIn a b (next s)

end TwoLevelDecisionTree

abbrev DecisionHistory (I : Type u) (S : I → Type v) := List (Sigma S)

noncomputable def policyTranscript
    {I : Type u} {S : I → Type v} {Ω : Type w}
    (π : DecisionHistory I S → Option I)
    (X : (i : I) → Ω → S i) : ℕ → Ω → DecisionHistory I S
  | 0, _ => []
  | n + 1, ω =>
      let h := policyTranscript π X n ω
      match π h with
      | none => h
      | some i => h ++ [⟨i, X i ω⟩]

def policyNoRepeat
    {I : Type u} {S : I → Type v} {Ω : Type w}
    (π : DecisionHistory I S → Option I)
    (X : (i : I) → Ω → S i) : Prop :=
  ∀ n ω i, π (policyTranscript π X n ω) = some i →
    ∀ v : S i,
      (⟨i, v⟩ : Sigma S) ∉ policyTranscript π X n ω

def policyStopsAt
    {I : Type u} {S : I → Type v} {Ω : Type w}
    (π : DecisionHistory I S → Option I)
    (X : (i : I) → Ω → S i)
    (τ : Ω → ℕ∞) : Prop :=
  ∀ ω,
    (τ ω = ⊤ ↔ ∀ n, π (policyTranscript π X n ω) ≠ none) ∧
    (∀ n : ℕ,
      τ ω = n ↔
        π (policyTranscript π X n ω) = none ∧
          ∀ k < n, π (policyTranscript π X k ω) ≠ none)

noncomputable def terminalTranscript
    {I : Type u} {S : I → Type v} {Ω : Type w}
    (π : DecisionHistory I S → Option I)
    (X : (i : I) → Ω → S i) : Ω → (ℕ → DecisionHistory I S) :=
  fun ω n => policyTranscript π X n ω

def MeasurableIn
    {α : Type u} {β : Type v}
    (mα : MeasurableSpace α) (mβ : MeasurableSpace β)
    (f : α → β) : Prop :=
  @Measurable α β mα mβ f

def MeasurableSetIn
    {α : Type u} (mα : MeasurableSpace α) (s : Set α) : Prop :=
  mα.MeasurableSet' s

def NullSandwich
    {Ω : Type u} (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (base : MeasurableSpace Ω) (s : Set Ω) : Prop :=
  ∃ u v : Set Ω,
    MeasurableSetIn base u ∧ MeasurableSetIn base v ∧
      u ⊆ s ∧ s ⊆ v ∧ P (v \ u) = 0

def IsCompletedTranscript
    {Ω : Type u} (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    {H : Type v} (tr : Ω → H) (m : MeasurableSpace Ω) : Prop :=
  MeasurableSpace.comap tr (⊤ : MeasurableSpace H) ≤ mΩ ∧
    m ≤ mΩ ∧
    ∀ s : Set Ω,
      MeasurableSetIn m s ↔
        NullSandwich mΩ P
          (MeasurableSpace.comap tr (⊤ : MeasurableSpace H)) s

def TranscriptStoppingTime
    {Ω : Type u} (F : ℕ → MeasurableSpace Ω)
    (τ : Ω → ℕ∞) : Prop :=
  ∀ t : ℕ,
    (F t).MeasurableSet' {ω | τ ω ≤ (t : ℕ∞)}

noncomputable def weightedTreeValue
    {I : Type u} {S : I → Type v} {R : Type w}
    (p : R → ℝ) (trees : R → TwoLevelDecisionTree I S)
    (X : (i : I) → Ω → S i) (ω : Ω) : ℝ :=
  ∑' r, p r * TwoLevelDecisionTree.eval (trees r) (fun i => X i ω)

noncomputable def transcriptArea
    {Ω : Type u} (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (F : ℕ → MeasurableSpace Ω) (μ : Ω → ℝ) (τ : Ω → ℕ∞) : ℝ :=
  ∑' t : ℕ, ∫ ω,
    (if (t : ℕ∞) < τ ω then (1 : ℝ) else 0) *
      (@ProbabilityTheory.condVar Ω mΩ (F t) μ P ω) ∂P

def IsDeterminingPolicy
    {I : Type u} {S : I → Type v} {Ω : Type w}
    (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (X : (i : I) → Ω → S i) (μ : Ω → ℝ)
    (π : DecisionHistory I S → Option I) (τ : Ω → ℕ∞)
    (F : ℕ → MeasurableSpace Ω) (Ftop : MeasurableSpace Ω) : Prop :=
  policyNoRepeat π X ∧
    policyStopsAt π X τ ∧
    (∀ t, IsCompletedTranscript mΩ P
      (policyTranscript π X t) (F t)) ∧
    TranscriptStoppingTime F τ ∧
    IsCompletedTranscript mΩ P (terminalTranscript π X) Ftop ∧
    MeasurableIn Ftop (borel ℝ) μ

def signValue (s : Bool) : ℝ :=
  if s then 1 else -1

noncomputable def twoSignProductTree (a b : ℝ) :
    TwoLevelDecisionTree (Fin 2) (fun _ => Bool) :=
  .query 0 0 (fun s₀ =>
    .query 1 1 (fun s₁ =>
      .leaf ((a + b) / 2 + ((b - a) / 2) *
        signValue s₀ * signValue s₁)))

noncomputable def twoSignMixture
    {Ω : Type u} (a b : ℝ) (X : Fin 2 → Ω → Bool) (ω : Ω) : ℝ :=
  weightedTreeValue (fun _ : Unit => (1 : ℝ))
    (fun _ : Unit => twoSignProductTree a b) X ω

def UniformTwoSigns
    {Ω : Type u} (mΩ : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (X : Fin 2 → Ω → Bool) : Prop :=
  (∀ i, MeasurableIn mΩ (⊤ : MeasurableSpace Bool) (X i)) ∧
    (∀ i,
      P {ω | X i ω = true} = ENNReal.ofReal (1 / 2 : ℝ) ∧
      P {ω | X i ω = false} = ENNReal.ofReal (1 / 2 : ℝ)) ∧
    @iIndepFun Ω (Fin 2) mΩ (fun _ => Bool)
      (fun _ => ⊤) X P

noncomputable def sharpBoundK2Sharpness (a b : ℝ) : Prop :=
  a ≤ b →
  TwoLevelDecisionTree.leveledFrom 0 (twoSignProductTree a b) ∧
    TwoLevelDecisionTree.alignedWith (fun i : Fin 2 => i)
      (twoSignProductTree a b) ∧
    TwoLevelDecisionTree.levelOneAt 0 (twoSignProductTree a b) ∧
    TwoLevelDecisionTree.leavesIn a b (twoSignProductTree a b) ∧
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω)
      (P : @Measure Ω mΩ) (X : Fin 2 → Ω → Bool),
      @IsProbabilityMeasure Ω mΩ P ∧
      UniformTwoSigns mΩ P X ∧
      (∃ (π : DecisionHistory (Fin 2) (fun _ => Bool) → Option (Fin 2))
        (τ : Ω → ℕ∞)
        (F : ℕ → MeasurableSpace Ω)
        (Ftop : MeasurableSpace Ω),
        IsDeterminingPolicy mΩ P X (twoSignMixture a b X)
          π τ F Ftop ∧
        transcriptArea mΩ P F (twoSignMixture a b X) τ =
          (2 : ℝ) * (b - a) ^ 2 / 4) ∧
      (∀ (π : DecisionHistory (Fin 2) (fun _ => Bool) → Option (Fin 2))
        (τ : Ω → ℕ∞)
        (F : ℕ → MeasurableSpace Ω)
        (Ftop : MeasurableSpace Ω),
        IsDeterminingPolicy mΩ P X (twoSignMixture a b X)
          π τ F Ftop →
        (2 : ℝ) * (b - a) ^ 2 / 4 ≤
          transcriptArea mΩ P F (twoSignMixture a b X) τ)

def sharpBoundK2SingleLevelOneCoordinate
    {I : Type u} [Countable I]
    (S : I → Type v) [∀ i, Fintype (S i)]
    {Ω : Type w} (mΩ : MeasurableSpace Ω)
    (P : @Measure Ω mΩ) (hP : @IsProbabilityMeasure Ω mΩ P)
    (X : (i : I) → Ω → S i)
    (hX : ∀ i, MeasurableIn mΩ (⊤ : MeasurableSpace (S i)) (X i))
    (hindep : @iIndepFun Ω I mΩ S (fun i => ⊤) X P)
    {R : Type z} (p : R → ℝ)
    (trees : R → TwoLevelDecisionTree I S)
    (hsupport : Set.Countable (Function.support p))
    (hp : ∀ r, 0 ≤ p r)
    (hpsum : ∑' r, p r = 1)
    (a b : ℝ) (hab : a ≤ b)
    (ell : I → Fin 2) (q : I)
    (htrees : ∀ r,
      TwoLevelDecisionTree.leveledFrom 0 (trees r) ∧
      TwoLevelDecisionTree.alignedWith ell (trees r) ∧
      TwoLevelDecisionTree.levelOneAt q (trees r) ∧
      TwoLevelDecisionTree.leavesIn a b (trees r)) : Prop :=
  ∃ (π : DecisionHistory I S → Option I)
    (τ : Ω → ℕ∞)
    (F : ℕ → MeasurableSpace Ω)
    (Ftop : MeasurableSpace Ω),
    IsDeterminingPolicy mΩ P X (weightedTreeValue p trees X)
      π τ F Ftop ∧
    transcriptArea mΩ P F (weightedTreeValue p trees X) τ ≤
      (2 : ℝ) * (b - a) ^ 2 / 4 ∧
    sharpBoundK2Sharpness a b

end MathlibPlus.Open.SharpBoundK2
