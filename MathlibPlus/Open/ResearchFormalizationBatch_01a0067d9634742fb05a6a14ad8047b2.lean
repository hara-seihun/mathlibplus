import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open

noncomputable def rfCrossingRelation {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (v w : V) : Prop :=
  G.Adj v w ∧ ((v ∈ S) ≠ (w ∈ S))

def rfCrossingGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (rfCrossingRelation G S)

noncomputable def rfInternalEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Set.ncard {p : V × V | G.Adj p.1 p.2 ∧ ((p.1 ∈ S) = (p.2 ∈ S))} / 2

noncomputable def rfCutEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Set.ncard {p : V × V | rfCrossingRelation G S p.1 p.2} / 2

def rfTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, a ≠ b → b ≠ c → c ≠ a →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

def rfMaximumCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ T : Finset V, rfCutEdgeCount G T ≤ rfCutEdgeCount G S

def rfClaim46797 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V),
    rfTriangleFree G →
    rfMaximumCut G S →
    SimpleGraph.IsAcyclic (rfCrossingGraph G S) →
    rfInternalEdgeCount G S ≤ Fintype.card V ^ 2 / 25 ∧
      (rfInternalEdgeCount G S = Fintype.card V ^ 2 / 25 →
        Nonempty (G ≃g SimpleGraph.cycleGraph 5))

def rfInternalRelation {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (v w : V) : Prop :=
  G.Adj v w ∧ ¬ ((v ∈ S) ≠ (w ∈ S))

def rfLayerConsecutive {V : Type*} {d : ℕ}
    (layers : Fin (d + 1) → Finset V) (v w : V) : Prop :=
  ∃ i j : Fin (d + 1),
    v ∈ layers i ∧ w ∈ layers j ∧
      (i.val + 1 = j.val ∨ j.val + 1 = i.val)

def rfLayeredPresentation {V : Type*} [Fintype V] [DecidableEq V]
    {d : ℕ} (G : SimpleGraph V) (S : Finset V)
    (layers : Fin (d + 1) → Finset V) : Prop :=
  (∀ i, (layers i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (layers i) (layers j)) ∧
  (∀ v, ∃ i, v ∈ layers i) ∧
  (∀ ⦃v w : V⦄, rfCrossingRelation G S v w →
    rfLayerConsecutive layers v w) ∧
  (∀ ⦃v w : V⦄, rfInternalRelation G S v w →
    ((v ∈ layers (0 : Fin (d + 1)) ∧ w ∈ layers (Fin.last d)) ∨
      (w ∈ layers (0 : Fin (d + 1)) ∧ v ∈ layers (Fin.last d))))

def rfCompleteConsecutive {V : Type*} {d : ℕ}
    (G : SimpleGraph V) (layers : Fin (d + 1) → Finset V) : Prop :=
  ∀ ⦃i j : Fin (d + 1)⦄, i.val + 1 = j.val →
    ∀ ⦃v w : V⦄, v ∈ layers i → w ∈ layers j → G.Adj v w

def rfCompleteEnds {V : Type*} {d : ℕ}
    (G : SimpleGraph V) (layers : Fin (d + 1) → Finset V) : Prop :=
  ∀ ⦃v w : V⦄,
    v ∈ layers (0 : Fin (d + 1)) → w ∈ layers (Fin.last d) → G.Adj v w

def rfClaim46799 : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}
    (G : SimpleGraph V) (S : Finset V)
    (layers : Fin (d + 1) → Finset V),
    rfTriangleFree G →
    rfMaximumCut G S →
    rfLayeredPresentation G S layers →
    rfInternalEdgeCount G S ≤ Fintype.card V ^ 2 / 25 ∧
      (rfInternalEdgeCount G S = Fintype.card V ^ 2 / 25 ↔
        (d = 4 ∧
          (∀ i, (layers i).card = (layers (0 : Fin (d + 1))).card) ∧
          rfCompleteConsecutive G layers ∧
          rfCompleteEnds G layers))

def rfSign (b : Bool) : ℝ :=
  if b then 1 else -1

abbrev rfOracleWorld : Type := Fin 5 → Bool

def rfA : Fin 5 := 0
def rfB : Fin 5 := 1
def rfC : Fin 5 := 2
def rfD : Fin 5 := 3
def rfE : Fin 5 := 4

def rfT1 (ω : rfOracleWorld) : ℝ :=
  if ω rfA = false then -rfSign (ω rfC) else -rfSign (ω rfB)

def rfT2 (ω : rfOracleWorld) : ℝ :=
  if ω rfD = false then -rfSign (ω rfC) else -rfSign (ω rfB)

def rfT3 (ω : rfOracleWorld) : ℝ :=
  if ω rfA = false then -rfSign (ω rfE) else -rfSign (ω rfD)

noncomputable def rfMu60091 (ω : rfOracleWorld) : ℝ :=
  (19 * rfT1 ω + 20 * rfT2 ω + 2 * rfT3 ω) / 41

def rfPolicy60091 (ω : rfOracleWorld) : List (Fin 5) :=
  rfB :: rfC ::
    if ω rfB = false ∧ ω rfC = false then
      rfA :: if ω rfA = false then [rfE] else [rfD]
    else if ω rfB = false ∧ ω rfC = true then
      rfA :: rfD :: if ω rfA = false then [rfE] else []
    else if ω rfB = true ∧ ω rfC = false then
      rfD :: rfA :: if ω rfA = false then [rfE] else []
    else
      rfA :: if ω rfA = false then [rfE] else [rfD]

def rfListAt {α : Type*} (xs : List α) (n : ℕ) : Option α :=
  if h : n < xs.length then some (xs.get ⟨n, h⟩) else none

def rfSameTranscript60091
    (π : rfOracleWorld → List (Fin 5)) (m : ℕ)
    (ω ω' : rfOracleWorld) : Prop :=
  List.take m (π ω) = List.take m (π ω') ∧
    ∀ j ∈ List.take m (π ω), ω j = ω' j

noncomputable def rfTranscriptClass60091
    (π : rfOracleWorld → List (Fin 5)) (m : ℕ)
    (ω : rfOracleWorld) : Finset rfOracleWorld := by
  classical
  exact Finset.univ.filter (fun ω' => rfSameTranscript60091 π m ω ω')

noncomputable def rfTranscriptMean60091
    (π : rfOracleWorld → List (Fin 5)) (m : ℕ)
    (ω : rfOracleWorld) : ℝ :=
  let C := rfTranscriptClass60091 π m ω
  (∑ ω' ∈ C, rfMu60091 ω') / (C.card : ℝ)

noncomputable def rfPosteriorVariance60091
    (π : rfOracleWorld → List (Fin 5)) (m : ℕ)
    (ω : rfOracleWorld) : ℝ :=
  let C := rfTranscriptClass60091 π m ω
  let meanValue := rfTranscriptMean60091 π m ω
  (∑ ω' ∈ C, (rfMu60091 ω' - meanValue) ^ 2) / (C.card : ℝ)

noncomputable def rfRootInclusiveArea60091
    (π : rfOracleWorld → List (Fin 5)) : ℝ :=
  ∑' m : ℕ,
    (∑ ω : rfOracleWorld, rfPosteriorVariance60091 π m ω) /
      (Fintype.card rfOracleWorld : ℝ)

def rfAdaptiveOrder60091
    (π : rfOracleWorld → List (Fin 5)) : Prop :=
  ∀ ω ω' m, rfSameTranscript60091 π m ω ω' →
    rfListAt (π ω) m = rfListAt (π ω') m

def rfPolicyLegal60091
    (π : rfOracleWorld → List (Fin 5)) : Prop :=
  (∀ ω, (π ω).Nodup) ∧
  (∀ ω, (π ω).length ≤ 5) ∧
  rfAdaptiveOrder60091 π ∧
  (∀ ω ω',
    rfSameTranscript60091 π (π ω).length ω ω' →
      rfMu60091 ω = rfMu60091 ω')

def rfClaim60091 : Prop :=
  rfPolicyLegal60091 rfPolicy60091 ∧
  (∃ ω, (rfPolicy60091 ω).length = 5) ∧
  rfRootInclusiveArea60091 rfPolicy60091 = (9917 : ℝ) / 6724 ∧
  (9917 : ℝ) / 6724 < 2

abbrev rfBoolWorld (J : Type*) := J → Bool

abbrev rfDepthTwoBranch (J : Type*) :=
  Sum Bool (J × (Bool → Bool))

abbrev rfDepthTwoTree (J : Type*) (_i : J) :=
  Bool → rfDepthTwoBranch J

def rfTreeUsesNoRepeat {J : Type*} (i : J)
    (T : rfDepthTwoTree J i) : Prop :=
  ∀ u, match T u with
    | Sum.inl _ => True
    | Sum.inr (j, _) => j ≠ i

noncomputable def rfTreeValue {J : Type*} [DecidableEq J]
    (i : J) (T : rfDepthTwoTree J i) (ω : rfBoolWorld J) : ℝ :=
  match T (ω i) with
  | Sum.inl b => rfSign b
  | Sum.inr (j, f) => rfSign (f (ω j))

def rfProbabilityWeights {α : Type*} [Fintype α]
    (p : α → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x : α, p x = 1

def rfSupportedDepthTwo {J : Type*} [Fintype J] [DecidableEq J]
    {i : J} (ν : rfDepthTwoTree J i → ℝ) : Prop :=
  ∀ T, ν T > 0 → rfTreeUsesNoRepeat i T

noncomputable def rfMixtureMean {J : Type*} [Fintype J] [DecidableEq J]
    {i : J} (ν : rfDepthTwoTree J i → ℝ)
    (ω : rfBoolWorld J) : ℝ :=
  ∑ T : rfDepthTwoTree J i, ν T * rfTreeValue i T ω

noncomputable def rfUniformAverage {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  (∑ x : α, f x) / (Fintype.card α : ℝ)

noncomputable def rfUniformVariance {α : Type*} [Fintype α]
    (f : α → ℝ) : ℝ :=
  let μ := rfUniformAverage f
  rfUniformAverage (fun x => (f x - μ) ^ 2)

noncomputable def rfSlice {J : Type*} [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (i : J) (u : Bool)
    (x : rfBoolWorld J) : ℝ :=
  g (Function.update x i u)

noncomputable def rfWalshConstant {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (i : J) (u : Bool) : ℝ :=
  rfUniformAverage (rfSlice g i u)

noncomputable def rfWalshCoefficient {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (i : J) (u : Bool) (j : J) : ℝ :=
  rfUniformAverage (fun x => rfSlice g i u x * rfSign (x j))

def rfAffineWalshSlice {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (i : J) : Prop :=
  ∀ u x,
    rfSlice g i u x =
      rfWalshConstant g i u +
        (Finset.univ.erase i).sum
          (fun j => rfWalshCoefficient g i u j * rfSign (x j))

abbrev rfRemaining (J : Type*) (i : J) :=
  {j : J // j ≠ i}

def rfBirkhoffRect {α : Type*} {β : Type*}
    [Fintype α] [Fintype β]
    (X : α → β → ℝ) : Prop :=
  (∀ a b, 0 ≤ X a b) ∧
  (∀ a, ∑ b : β, X a b = 1) ∧
  (∀ b, ∑ a : α, X a b = 1)

noncomputable def rfBirkhoffCost
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (a : J → ℝ)
    (X : rfRemaining J i →
      Fin (Fintype.card (rfRemaining J i)) → ℝ) : ℝ :=
  ∑ j : rfRemaining J i,
    ∑ r : Fin (Fintype.card (rfRemaining J i)),
      ((r.val + 1 : ℕ) : ℝ) * (a j.1) ^ 2 * X j r

noncomputable def rfMinBirkhoffCost
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (a : J → ℝ) : ℝ :=
  sInf {z : ℝ |
    ∃ X : rfRemaining J i →
      Fin (Fintype.card (rfRemaining J i)) → ℝ,
      rfBirkhoffRect X ∧ z = rfBirkhoffCost i a X}

abbrev rfSchedule (J : Type*) [Fintype J] :=
  (rfBoolWorld J) → Fin (Fintype.card J + 1) → Option J

def rfScheduleValue {J : Type*} [Fintype J]
    (σ : rfSchedule J) (ω : rfBoolWorld J) (n : ℕ) : Option J :=
  if h : n < Fintype.card J + 1 then σ ω ⟨n, h⟩ else none

def rfObservationAt {J : Type*} [Fintype J]
    (σ : rfSchedule J) (ω : rfBoolWorld J) (n : ℕ) : Option (J × Bool) :=
  match rfScheduleValue σ ω n with
  | none => none
  | some j => some (j, ω j)

def rfSameScheduleHistory {J : Type*} [Fintype J]
    (σ : rfSchedule J) (m : ℕ)
    (ω ω' : rfBoolWorld J) : Prop :=
  ∀ n, n < m → rfObservationAt σ ω n = rfObservationAt σ ω' n

def rfScheduleLegal {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (σ : rfSchedule J) : Prop :=
  (∀ ω, rfScheduleValue σ ω 0 = some i) ∧
  (∀ ω ω' n,
    rfSameScheduleHistory σ n ω ω' →
      rfScheduleValue σ ω n = rfScheduleValue σ ω' n) ∧
  (∀ ω n j,
    rfScheduleValue σ ω n = some j →
      ∀ k, k < n → rfScheduleValue σ ω k ≠ some j) ∧
  (∀ ω j, j ≠ i → ∃ n, rfScheduleValue σ ω n = some j) ∧
  (∀ ω n, rfScheduleValue σ ω n = none →
    ∀ k, n ≤ k → rfScheduleValue σ ω k = none)

def rfRandomizedPolicy {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (p : rfSchedule J → ℝ) : Prop :=
  rfProbabilityWeights p ∧
  ∀ σ, p σ > 0 → rfScheduleLegal i σ

noncomputable def rfScheduleClass
    {J : Type*} [Fintype J] [DecidableEq J]
    (σ : rfSchedule J) (m : ℕ) (ω : rfBoolWorld J) : Finset (rfBoolWorld J) := by
  classical
  exact Finset.univ.filter (fun ω' => rfSameScheduleHistory σ m ω ω')

noncomputable def rfScheduleMean
    {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (σ : rfSchedule J)
    (m : ℕ) (ω : rfBoolWorld J) : ℝ :=
  let C := rfScheduleClass σ m ω
  (∑ ω' ∈ C, g ω') / (C.card : ℝ)

noncomputable def rfScheduleVariance
    {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (σ : rfSchedule J)
    (m : ℕ) (ω : rfBoolWorld J) : ℝ :=
  let C := rfScheduleClass σ m ω
  let meanValue := rfScheduleMean g σ m ω
  (∑ ω' ∈ C, (g ω' - meanValue) ^ 2) / (C.card : ℝ)

noncomputable def rfScheduleArea
    {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (σ : rfSchedule J) : ℝ :=
  ∑' m : ℕ,
    (∑ ω : rfBoolWorld J, rfScheduleVariance g σ m ω) /
      (Fintype.card (rfBoolWorld J) : ℝ)

noncomputable def rfRandomizedArea
    {J : Type*} [Fintype J] [DecidableEq J]
    (g : rfBoolWorld J → ℝ) (p : rfSchedule J → ℝ) : ℝ :=
  ∑ σ : rfSchedule J, p σ * rfScheduleArea g σ

noncomputable def rfAiStar
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (g : rfBoolWorld J → ℝ) : ℝ :=
  sInf {z : ℝ |
    ∃ p : rfSchedule J → ℝ,
      rfRandomizedPolicy i p ∧ z = rfRandomizedArea g p}

noncomputable def rfFormula60092
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (g : rfBoolWorld J → ℝ) : ℝ :=
  rfUniformVariance g +
    (1 / 2 : ℝ) *
      ∑ u : Bool,
        rfMinBirkhoffCost i
          (fun j => rfWalshCoefficient g i u j)

def rfOrderedAfterRoot
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (a : Bool → J → ℝ)
    (σ : rfSchedule J) (ω : rfBoolWorld J) : Prop :=
  ∀ r s : Fin (Fintype.card J + 1),
    1 ≤ r.val → r.val < s.val →
    ∀ j k,
      rfScheduleValue σ ω r.val = some j →
      rfScheduleValue σ ω s.val = some k →
      |a (ω i) j| ≥ |a (ω i) k|

def rfOrderedOptimizer
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) (a : Bool → J → ℝ)
    (p : rfSchedule J → ℝ) : Prop :=
  ∀ σ, p σ > 0 → ∀ ω, rfOrderedAfterRoot i a σ ω

abbrev rfBlockIndex {J : Type*} [Fintype J] [DecidableEq J]
    (i : J) :=
  Bool × (rfRemaining J i × Fin (Fintype.card (rfRemaining J i)))

def rfBlockDiagonalMatrix
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J)
    (X : Bool → rfRemaining J i →
      Fin (Fintype.card (rfRemaining J i)) → ℝ) :
    Matrix (rfBlockIndex i) (rfBlockIndex i) ℝ :=
  Matrix.diagonal (fun q => X q.1 q.2.1 q.2.2)

def rfBlockDiagonalPSD
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J)
    (X : Bool → rfRemaining J i →
      Fin (Fintype.card (rfRemaining J i)) → ℝ) : Prop :=
  Matrix.PosSemidef (rfBlockDiagonalMatrix i X)

def rfRowColumnSums
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J)
    (X : Bool → rfRemaining J i →
      Fin (Fintype.card (rfRemaining J i)) → ℝ) : Prop :=
  (∀ u j, ∑ r : Fin (Fintype.card (rfRemaining J i)), X u j r = 1) ∧
  (∀ u r, ∑ j : rfRemaining J i, X u j r = 1)

def rfDiagonalNonnegative
    {J : Type*} [Fintype J] [DecidableEq J]
    (i : J)
    (X : Bool → rfRemaining J i →
      Fin (Fintype.card (rfRemaining J i)) → ℝ) : Prop :=
  ∀ u j r, 0 ≤ X u j r

def rfParityTree {J : Type*} (i j : J) : rfDepthTwoTree J i :=
  fun u => Sum.inr (j, fun v => decide (u = v))

def rfParityFunction {J : Type*} (i j : J) (ω : rfBoolWorld J) : ℝ :=
  rfSign (ω i) * rfSign (ω j)

def rfClaim60092 : Prop :=
  ∀ {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (i : J) (ν : rfDepthTwoTree J i → ℝ)
    (g : rfBoolWorld J → ℝ),
    (rfProbabilityWeights ν ∧
      rfSupportedDepthTwo ν ∧
      (∀ ω, g ω = rfMixtureMean ν ω)) →
    rfAffineWalshSlice g i ∧
    (∀ u,
      |rfWalshConstant g i u| +
        (Finset.univ.erase i).sum
          (fun j => |rfWalshCoefficient g i u j|) ≤ 1) ∧
    rfAiStar i g = rfFormula60092 i g ∧
    (∀ u, ∃ X : rfRemaining J i →
        Fin (Fintype.card (rfRemaining J i)) → ℝ,
        rfBirkhoffRect X ∧
          rfBirkhoffCost i
            (fun j => rfWalshCoefficient g i u j) X =
            rfMinBirkhoffCost i
              (fun j => rfWalshCoefficient g i u j)) ∧
    (∀ X : Bool → rfRemaining J i →
        Fin (Fintype.card (rfRemaining J i)) → ℝ,
      ((∀ u, rfBirkhoffRect (X u)) ↔
        (rfRowColumnSums i X ∧ rfBlockDiagonalPSD i X))) ∧
    (∃ p : rfSchedule J → ℝ,
      rfRandomizedPolicy i p ∧
      rfAiStar i g = rfRandomizedArea g p ∧
      rfRandomizedArea g p = rfFormula60092 i g ∧
      rfOrderedOptimizer i
        (fun u j => rfWalshCoefficient g i u j) p) ∧
    rfAiStar i g ≤ 2 ∧
    (∀ j, j ≠ i →
      rfTreeUsesNoRepeat i (rfParityTree i j) ∧
      (∀ ω,
        rfTreeValue i (rfParityTree i j) ω = rfParityFunction i j ω) ∧
      rfAiStar i (rfParityFunction i j) = 2)

end MathlibPlus.Open
