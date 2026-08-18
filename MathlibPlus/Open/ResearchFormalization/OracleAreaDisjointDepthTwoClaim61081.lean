import MathlibPlus.Open.Analysis.OracleAreaDepthTwoFiveFourths

open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaDisjointDepthTwoClaim61081

noncomputable section
open Classical

abbrev Sign := MathlibPlus.Open.Analysis.Sign
abbrev Oracle (I : Type*) := I → Sign
abbrev BooleanFunction (I : Type*) := Oracle I → Sign
abbrev BooleanLaw (I : Type*) := BooleanFunction I → ℝ
abbrev RevealTranscript (I : Type*) := List (I × Sign)
abbrev RevealPolicy (I : Type*) := RevealTranscript I → Option I
abbrev ActionLaw (I : Type*) := Option I → ℝ
abbrev RandomizedPolicy (I : Type*) := RevealTranscript I → ActionLaw I

/-- The law's positive-mass support.  A `tsum` law permits finite and countably
supported mixtures without replacing an infinite support by a finite record. -/
def lawSupport {I : Type*} (Λ : BooleanLaw I) : Set (BooleanFunction I) :=
  {T | 0 < Λ T}

def realProbabilityLaw {α : Type*} (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑' a, p a = 1

def probabilityLaw {I : Type*} (Λ : BooleanLaw I) : Prop :=
  realProbabilityLaw Λ

def finiteSupport {I : Type*} (Λ : BooleanLaw I) : Prop :=
  Set.Finite (lawSupport Λ)

def lawMean {I : Type*} (Λ : BooleanLaw I) (O : Oracle I) : ℝ :=
  ∑' T, Λ T * MathlibPlus.Open.Analysis.signValue (T O)

def nonconstantMass {I : Type*} (Λ : BooleanLaw I) : ℝ :=
  ∑' T, if MathlibPlus.Open.Analysis.SignFunctionNonconstant T then Λ T else 0

def depthTwoLaw {I : Type*} (Λ : BooleanLaw I) : Prop :=
  ∀ T, T ∈ lawSupport Λ →
    MathlibPlus.Open.Analysis.ComputableBySignDecisionTreeDepthTwo T

def pairwiseDisjointRelevantSupport {I : Type*} (Λ : BooleanLaw I) : Prop :=
  ∀ T U,
    T ∈ lawSupport Λ → U ∈ lawSupport Λ → T ≠ U →
      MathlibPlus.Open.Analysis.SignFunctionNonconstant T →
      MathlibPlus.Open.Analysis.SignFunctionNonconstant U →
      Disjoint
        (MathlibPlus.Open.Analysis.SignFunctionDependsOn T)
        (MathlibPlus.Open.Analysis.SignFunctionDependsOn U)

/-- The event that a finite reveal transcript is compatible with an oracle. -/
def transcriptCompatible {I : Type*}
    (h : RevealTranscript I) (O : Oracle I) : Prop :=
  ∀ p ∈ h, O p.1 = p.2

def recordedSign {I : Type*} (h : RevealTranscript I) (i : I) : Option Sign :=
  (h.find? (fun p => p.1 = i)).map Prod.snd

def transcriptStep {I : Type*} (h : RevealTranscript I)
    (O : Oracle I) (a : Option I) : RevealTranscript I :=
  match a with
  | none => h
  | some i => h ++ [(i, O i)]

def historyAt {I : Type*} (π : RevealPolicy I) (O : Oracle I) : ℕ → RevealTranscript I
  | 0 => []
  | m + 1 =>
      let h := historyAt π O m
      transcriptStep h O (π h)

def legalPolicy {I : Type*} (π : RevealPolicy I) : Prop :=
  ∀ h i, π h = some i → recordedSign h i = none

def revealFiltration {I : Type*} (π : RevealPolicy I) (m : ℕ) :
    MeasurableSpace (Oracle I) :=
  MeasurableSpace.comap
    (fun O => historyAt π O m)
    (⊤ : MeasurableSpace (RevealTranscript I))

def limitFiltration {I : Type*} (π : RevealPolicy I) : MeasurableSpace (Oracle I) :=
  ⨆ m : ℕ, revealFiltration π m

def measurableIn {Ω : Type*} (m : MeasurableSpace Ω)
    (f : Ω → ℝ) : Prop :=
  @Measurable Ω ℝ m inferInstance f

def cellMeasurable {I : Type*} (μ : Oracle I → ℝ)
    (h : RevealTranscript I) : Prop :=
  ∀ O O', transcriptCompatible h O → transcriptCompatible h O' → μ O = μ O'

def stoppedWhenMeasurable {I : Type*} (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  ∀ O m,
    (π (historyAt π O m) = none ↔
      cellMeasurable μ (historyAt π O m))

def limitDeterminesTarget {I : Type*} (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  measurableIn (limitFiltration π) μ

def infiniteNonconstantSupport {I : Type*} (Λ : BooleanLaw I) : Prop :=
  Set.Infinite
    {T | T ∈ lawSupport Λ ∧
      MathlibPlus.Open.Analysis.SignFunctionNonconstant T}

def policyArea {I : Type*} (P : Measure (Oracle I))
    (π : RevealPolicy I) (μ : Oracle I → ℝ) : ℝ :=
  ∑' m : ℕ,
    MathlibPlus.Open.Analysis.expectedConditionalVariance
      P (revealFiltration π m) μ

def deterministicDetermines {I : Type*} (π : RevealPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  ∀ O, ∃ m, cellMeasurable μ (historyAt π O m)

/-- An action law is a probability distribution on the next coordinate or stop. -/
def actionProbabilityLaw {I : Type*} (p : ActionLaw I) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑' a, p a = 1

def actionContains {I : Type*} (h : RevealTranscript I) (i : I) : Prop :=
  recordedSign h i ≠ none

def randomizedLegal {I : Type*} (κ : RandomizedPolicy I) : Prop :=
  ∀ h,
    actionProbabilityLaw (κ h) ∧
      ∀ i, actionContains h i → κ h (some i) = 0

def randomizedTranscript {I : Type*} (h : RevealTranscript I)
    (O : Oracle I) : List (Option I) → RevealTranscript I
  | [] => h
  | a :: as => randomizedTranscript (transcriptStep h O a) O as

def randomizedPathWeight {I : Type*} (κ : RandomizedPolicy I)
    (h : RevealTranscript I) (O : Oracle I) : List (Option I) → ℝ
  | [] => 1
  | a :: as =>
      κ h a * randomizedPathWeight κ (transcriptStep h O a) O as

def randomizedTranscriptAt {I : Type*} (O : Oracle I)
    (m : ℕ) (a : Fin m → Option I) : RevealTranscript I :=
  randomizedTranscript [] O (List.ofFn a)

def randomizedPathWeightAt {I : Type*} (κ : RandomizedPolicy I)
    (O : Oracle I) (m : ℕ) (a : Fin m → Option I) : ℝ :=
  randomizedPathWeight κ [] O (List.ofFn a)

def cellSet {I : Type*} (h : RevealTranscript I) : Set (Oracle I) :=
  {O | transcriptCompatible h O}

def cellMass {I : Type*} (P : Measure (Oracle I))
    (h : RevealTranscript I) : ℝ :=
  (P (cellSet h)).toReal

noncomputable def cellMean {I : Type*} (P : Measure (Oracle I))
    (μ : Oracle I → ℝ) (h : RevealTranscript I) : ℝ :=
  if cellMass P h = 0 then 0 else
    (∫ O, μ O ∂(P.restrict (cellSet h))) / cellMass P h

noncomputable def cellVariance {I : Type*} (P : Measure (Oracle I))
    (μ : Oracle I → ℝ) (h : RevealTranscript I) : ℝ :=
  if cellMass P h = 0 then 0 else
    (∫ O, (μ O - cellMean P μ h) ^ 2 ∂(P.restrict (cellSet h))) /
      cellMass P h

def randomizedDetermines {I : Type*} (κ : RandomizedPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  ∀ O (a : ℕ → Option I),
    (∀ m,
      0 < randomizedPathWeightAt κ O m
        (fun j => a j)) →
      ∃ m,
        cellMeasurable μ
          (randomizedTranscriptAt O m (fun j => a j))

def randomizedPolicyArea {I : Type*} (P : Measure (Oracle I))
    (κ : RandomizedPolicy I) (μ : Oracle I → ℝ) : ℝ :=
  ∑' m : ℕ,
    ∫ O,
      ∑' a : Fin m → Option I,
        randomizedPathWeightAt κ O m a *
          cellVariance P μ (randomizedTranscriptAt O m a) ∂P

def randomizedLegalDetermining {I : Type*} (κ : RandomizedPolicy I)
    (μ : Oracle I → ℝ) : Prop :=
  randomizedLegal κ ∧ randomizedDetermines κ μ

def orderPolicy {I : Type*} (order : List I)
    (μ : Oracle I → ℝ) : RevealPolicy I :=
  fun h =>
    if cellMeasurable μ h then none
    else
      match order.drop h.length with
      | [] => none
      | i :: _ => if recordedSign h i = none then some i else none

def validNonadaptiveOrder {I : Type*} (order : List I)
    (r y z : I) : Prop :=
  order.Nodup ∧ r ∈ order ∧ y ∈ order ∧ z ∈ order

def nonadaptiveOrderLaw {I : Type*} (ρ : List I → ℝ)
    (r y z : I) : Prop :=
  realProbabilityLaw ρ ∧
    ∀ order, order ∈ {o | 0 < ρ o} →
      validNonadaptiveOrder order r y z

def nonadaptiveRandomizedArea {I : Type*} (P : Measure (Oracle I))
    (ρ : List I → ℝ) (μ : Oracle I → ℝ) (r y z : I) : ℝ :=
  ∑' order, ρ order * policyArea P (orderPolicy order μ) μ

def pointOrderLaw {I : Type*} (order₀ : List I) : List I → ℝ :=
  fun order => if order = order₀ then 1 else 0

def selector {I : Type*} (r y z : I) : Oracle I → Sign :=
  fun O => if O r = MathlibPlus.Open.Analysis.posSign then O y else O z

def constantFunction {I : Type*} (s : Sign) : BooleanFunction I :=
  fun _ => s

def selectorMixtureLaw {I : Type*} (q : ℝ) (r y z : I) : BooleanLaw I :=
  fun T =>
    if T = selector r y z then q
    else if T = constantFunction MathlibPlus.Open.Analysis.negSign then 1 - q
    else 0

def selectorPointLaw {I : Type*} (r y z : I) : BooleanLaw I :=
  fun T => if T = selector r y z then 1 else 0

def selectorPolicy {I : Type*} (r y z : I) : RevealPolicy I :=
  fun h =>
    match recordedSign h r with
    | none => some r
    | some s =>
      if s = MathlibPlus.Open.Analysis.posSign then
        if recordedSign h y = none then some y else none
      else if recordedSign h z = none then some z else none

def selectorSharpness61081 {I : Type*} [Countable I]
    (r y z : I) (P : Measure (Oracle I)) : Prop :=
  r ≠ y ∧ r ≠ z ∧ y ≠ z →
    MathlibPlus.Open.Analysis.IndependentUniformSigns P →
      (∀ q : ℝ, 0 < q → q ≤ 1 →
            let Λ := selectorMixtureLaw q r y z
            let μ := fun O => lawMean Λ O
            probabilityLaw Λ ∧
              depthTwoLaw Λ ∧
              pairwiseDisjointRelevantSupport Λ ∧
              nonconstantMass Λ = q ∧
              (∀ κ : RandomizedPolicy I,
                randomizedLegalDetermining κ μ →
                  2 * q ^ 2 ≤ randomizedPolicyArea P κ μ) ∧
              legalPolicy (selectorPolicy r y z) ∧
              stoppedWhenMeasurable (selectorPolicy r y z) μ ∧
              deterministicDetermines (selectorPolicy r y z) μ ∧
              policyArea P (selectorPolicy r y z) μ = 2 * q ^ 2) ∧
          (let Λ := selectorPointLaw r y z
           let μ := fun O => lawMean Λ O
           probabilityLaw Λ ∧
             depthTwoLaw Λ ∧
             pairwiseDisjointRelevantSupport Λ ∧
             nonconstantMass Λ = 1 ∧
             legalPolicy (selectorPolicy r y z) ∧
             stoppedWhenMeasurable (selectorPolicy r y z) μ ∧
             deterministicDetermines (selectorPolicy r y z) μ ∧
             policyArea P (selectorPolicy r y z) μ = 2 ∧
             (∀ ρ : List I → ℝ,
               nonadaptiveOrderLaw ρ r y z →
                 (9 / 4 : ℝ) ≤
                   nonadaptiveRandomizedArea P ρ μ r y z) ∧
             nonadaptiveRandomizedArea P (pointOrderLaw [y, r, z]) μ r y z =
               (9 / 4 : ℝ) ∧
             nonadaptiveRandomizedArea P (pointOrderLaw [z, r, y]) μ r y z =
               (9 / 4 : ℝ))

/-- Claim 61081: disjoint relevant-coordinate supports give a root-inclusive
adaptive area bound, including the countable-support limit and the sharp
coefficient and selector obstructions. -/
def depthTwoDisjointOracleArea_claim61081 : Prop :=
  (∀ (I : Type*) [Countable I] (Λ : BooleanLaw I)
      (P : Measure (Oracle I)),
      probabilityLaw Λ →
        depthTwoLaw Λ →
          pairwiseDisjointRelevantSupport Λ →
            MathlibPlus.Open.Analysis.IndependentUniformSigns P →
              let μ := fun O => lawMean Λ O
              let q := nonconstantMass Λ
              ∃ π : RevealPolicy I,
                legalPolicy π ∧
                  stoppedWhenMeasurable π μ ∧
                  limitDeterminesTarget π μ ∧
                  (infiniteNonconstantSupport Λ →
                    ∀ O m, π (historyAt π O m) ≠ none) ∧
                  policyArea P π μ ≤ 2 * q ^ 2 ∧
                  2 * q ^ 2 ≤ 2) ∧
  (∀ (I : Type*) [Countable I] (r y z : I) (P : Measure (Oracle I)),
    selectorSharpness61081 r y z P)

end

end MathlibPlus.Open.ResearchFormalization.OracleAreaDisjointDepthTwoClaim61081
