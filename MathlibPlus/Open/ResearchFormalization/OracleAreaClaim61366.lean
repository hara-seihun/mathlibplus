import MathlibPlus.Open.ResearchFormalization.OracleAreaCommonSupport.Claim61135

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61366

universe u

open MathlibPlus.Open.Analysis
open MathlibPlus.Open.ResearchFormalization.OracleAreaCommonSupport

attribute [local instance] Classical.decEq Classical.propDecidable

/-- A finite Rademacher oracle after irrelevant coordinates have been removed. -/
abbrev RademacherCube (I : Type*) := I → Bool

/-- A coordinate-answer transcript.  `none` means that the coordinate is still
unrevealed. -/
abbrev Transcript (I : Type*) := I → Option Bool

/-- A deterministic policy is a function of the preceding answer transcript;
`some i` charges one reveal of coordinate `i`, and `none` stops. -/
abbrev RevealPolicy (I : Type*) := Transcript I → Option I

def emptyTranscript {I : Type*} : Transcript I := fun _ => none

def updateTranscript {I : Type*} (h : Transcript I) (i : I) (b : Bool) :
    Transcript I :=
  Function.update h i (some b)

/-- The finite cell of cube points compatible with a transcript. -/
def transcriptCell {I : Type*} [Fintype I]
    (h : Transcript I) : Finset (RademacherCube I) :=
  (Finset.univ : Finset (RademacherCube I)).filter
    (fun x => ∀ i b, h i = some b → x i = b)

/-- Uniform averaging on the finite cube. -/
def uniformCubeAverage {I : Type*} [Fintype I]
    (g : RademacherCube I → ℝ) : ℝ :=
  (∑ x : RademacherCube I, g x) /
    (Fintype.card (RademacherCube I) : ℝ)

/-- Conditional mean and variance on a finite transcript cell. -/
def transcriptMean {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) (h : Transcript I) : ℝ :=
  (∑ x ∈ transcriptCell h, f x) /
    ((transcriptCell h).card : ℝ)

def transcriptVariance {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) (h : Transcript I) : ℝ :=
  (∑ x ∈ transcriptCell h,
      (f x - transcriptMean f h) ^ 2) /
    ((transcriptCell h).card : ℝ)

/-- Constancy of the target on a posterior cell, hence measurability from the
revealed transcript. -/
def targetDeterminedAt {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) (h : Transcript I) : Prop :=
  ∀ x y, x ∈ transcriptCell h → y ∈ transcriptCell h → f x = f y

/-- The retained coordinate set determines the target. -/
def targetDeterminedBySet {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) : Prop :=
  ∀ x y, (∀ i, i ∈ D → x i = y i) → f x = f y

/-- The transcript generated after `m` policy steps on an oracle point.  Once
`none` is returned, the transcript is held fixed at later times. -/
def policyTranscriptAt {I : Type*}
    (π : RevealPolicy I) (x : RademacherCube I) : ℕ → Transcript I
  | 0 => emptyTranscript
  | m + 1 =>
      let h := policyTranscriptAt π x m
      match π h with
      | none => h
      | some i => updateTranscript h i (x i)

/-- The set of coordinates present in a transcript. -/
def transcriptDomain {I : Type*} [Fintype I]
    (h : Transcript I) : Finset I :=
  (Finset.univ : Finset I).filter (fun i => (h i).isSome)

/-- Legality: every charged coordinate belongs to the retained finite set and
has not appeared in the preceding transcript. -/
def policyLegalOn {I : Type*} [Fintype I]
    (D : Finset I) (π : RevealPolicy I) : Prop :=
  ∀ h i, π h = some i → i ∈ D ∧ h i = none

/-- A policy has at most `t` charged reveals on every oracle branch. -/
def policyHorizonAtMost {I : Type*} [Fintype I]
    (D : Finset I) (π : RevealPolicy I) (t : ℕ) : Prop :=
  ∀ x,
    transcriptDomain (policyTranscriptAt π x (t + 1)) ⊆ D ∧
      (transcriptDomain (policyTranscriptAt π x (t + 1))).card ≤ t

/-- Endpoint posterior risk of a policy, after enough steps to exhaust the
retained finite coordinate set. -/
def policyEndpointRisk {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) (π : RevealPolicy I) : ℝ :=
  uniformCubeAverage (fun x =>
    transcriptVariance f (policyTranscriptAt π x D.card))

/-- Expected posterior variance at query time `m`. -/
def expectedPolicyVariance {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) (π : RevealPolicy I) (m : ℕ) : ℝ :=
  uniformCubeAverage (fun x =>
    transcriptVariance f (policyTranscriptAt π x m))

/-- Root-inclusive complete area, with the terminal zero-variance tail retained
as the later terms of the natural-number sum. -/
noncomputable def policyArea {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) (π : RevealPolicy I) : ℝ :=
  ∑' m : ℕ, expectedPolicyVariance f π m

/-- The target is measurable when the policy has stopped. -/
def policyComplete {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) (π : RevealPolicy I) : Prop :=
  ∀ x, ∃ m, m ≤ D.card ∧
    π (policyTranscriptAt π x m) = none ∧
      targetDeterminedAt f (policyTranscriptAt π x m)

/-- The separately optimized endpoint posterior-variance curve. -/
noncomputable def riskCurve {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) (t : ℕ) : ℝ :=
  sInf {a : ℝ |
    ∃ π : RevealPolicy I,
      policyLegalOn D π ∧
        policyHorizonAtMost D π t ∧
          a = policyEndpointRisk D f π}

/-- The pointwise-optimal risk-curve area `S(f)`. -/
noncomputable def riskCurveArea {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) : ℝ :=
  ∑ t ∈ Finset.range D.card, riskCurve D f t

/-- The Bellman-optimal root-inclusive complete area `A(f)`. -/
noncomputable def completeAreaMinimum {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) : ℝ :=
  sInf {a : ℝ |
    ∃ π : RevealPolicy I,
      policyLegalOn D π ∧
        policyComplete D f π ∧
          a = policyArea f π}

/-- A concrete finite randomization over deterministic policies. -/
def policyRandomization {I : Type*} [Fintype I]
    (ρ : RevealPolicy I → ℝ) : Prop :=
  (∀ π, 0 ≤ ρ π) ∧
    (∑ π : RevealPolicy I, ρ π) = 1

noncomputable def randomizedEndpointRisk {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) (t : ℕ)
    (ρ : RevealPolicy I → ℝ) : ℝ :=
  ∑ π : RevealPolicy I,
    ρ π *
      if policyLegalOn D π ∧ policyHorizonAtMost D π t then
        policyEndpointRisk D f π
      else 0

/-- Purification of a finite private random seed for a fixed endpoint-risk
optimization. -/
def randomizationPurifiesEndpointRisk {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ) (t : ℕ) : Prop :=
  ∀ ρ : RevealPolicy I → ℝ,
    policyRandomization ρ →
      (∀ π, ρ π ≠ 0 →
        policyLegalOn D π ∧ policyHorizonAtMost D π t) →
        ∃ π,
          policyLegalOn D π ∧
            policyHorizonAtMost D π t ∧
              policyEndpointRisk D f π ≤
                randomizedEndpointRisk D f t ρ

/-- A family of deterministic policies attaining every endpoint minimum. -/
def riskCurveMinimizerFamily {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ)
    (policies : ℕ → RevealPolicy I) : Prop :=
  ∀ t,
    policyLegalOn D (policies t) ∧
      policyHorizonAtMost D (policies t) t ∧
        policyEndpointRisk D f (policies t) = riskCurve D f t ∧
          (D.card ≤ t → policyComplete D f (policies t))

/-- The first dyadic phase whose horizon reaches the retained coordinate count. -/
def firstDyadicPhase (n L : ℕ) : Prop :=
  n ≤ 2 ^ L ∧
    ∀ j, j < L → 2 ^ j < n

def dyadicRevealBudget (L : ℕ) : ℕ := 2 ^ (L + 1) - 1

/-- Replay one policy on its own internal transcript, feeding it cached answers
from the global transcript at zero global charge. -/
def cachedPolicyRequestAux {I : Type*}
    (π : RevealPolicy I) (global internal : Transcript I) : ℕ → Option I
  | 0 => none
  | q + 1 =>
      match π internal with
      | none => none
      | some i =>
          match global i with
          | none => some i
          | some b =>
              cachedPolicyRequestAux π global
                (updateTranscript internal i b) q

noncomputable def cachedPolicyRequest {I : Type*} [Fintype I]
    (D : Finset I) (π : RevealPolicy I) (global : Transcript I) : Option I :=
  cachedPolicyRequestAux π global emptyTranscript (D.card + 1)

/-- The first still-unresolved request in the successive policies with horizons
`1,2,4,...`; each request is obtained from that phase's private transcript. -/
def dovetailPhaseRequest {I : Type*} [Fintype I]
    (D : Finset I) (policies : ℕ → RevealPolicy I)
    (global : Transcript I) : ℕ → Option I
  | 0 => cachedPolicyRequest D (policies 1) global
  | j + 1 =>
      match dovetailPhaseRequest D policies global j with
      | some i => some i
      | none => cachedPolicyRequest D (policies (2 ^ (j + 1))) global

/-- The actual deterministic cached dovetail policy. -/
def dovetailPolicy {I : Type*} [Fintype I]
    (D : Finset I) (f : RademacherCube I → ℝ)
    (policies : ℕ → RevealPolicy I) : RevealPolicy I :=
  fun h =>
    if targetDeterminedAt f h then none
    else dovetailPhaseRequest D policies h D.card

/-- A scalar record of the dyadic phase charge used in the factor-four estimate. -/
def dyadicPhaseCharge (r : ℕ → ℝ) (L : ℕ) : ℝ :=
  r 0 +
    ∑ j ∈ Finset.Icc 1 L,
      ((2 ^ j : ℕ) : ℝ) * r (2 ^ (j - 1))

/-- A finite mixture mean of Boolean-valued adaptive reveal trees. -/
def cubeSignEmbedding {I : Type*} (x : RademacherCube I) : I → ℝ :=
  fun i => if x i then 1 else -1

def finiteMixtureMean {I J : Type*} [Fintype J]
    (weights : J → ℝ) (trees : J → AdaptiveRevealTree I) :
    RademacherCube I → ℝ :=
  fun x =>
    ∑ j : J, weights j * adaptiveTreeRun (trees j) (cubeSignEmbedding x)

/-- Finite convex mixtures of legal Boolean trees of depth at most `k`. -/
def finiteDepthKMixture {I J : Type*} [Fintype J]
    (k : ℕ) (weights : J → ℝ)
    (trees : J → AdaptiveRevealTree I) : Prop :=
  (∀ j, 0 ≤ weights j) ∧
    (∑ j : J, weights j) = 1 ∧
      ∀ j, legalAdaptiveTree (trees j) ∧
        adaptiveTreeDepth (trees j) ≤ k

/-- Coordinates on which a target is genuinely nonconstant when that one
coordinate is toggled. -/
def coordinateRelevant {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) (i : I) : Prop :=
  ∃ x y,
    (∀ j, j ≠ i → x j = y j) ∧
      x i ≠ y i ∧ f x ≠ f y

noncomputable def relevantCoordinates {I : Type*} [Fintype I]
    (f : RademacherCube I → ℝ) : Finset I :=
  (Finset.univ : Finset I).filter (coordinateRelevant f)

/-- The finite-mixture subclass used by the campaign implications. -/
def finiteMixtureRiskCurveBound {I : Type u} [Fintype I]
    (C₀ : ℝ) (k : ℕ) : Prop :=
  ∀ (n : ℕ) (weights : Fin n → ℝ)
    (trees : Fin n → AdaptiveRevealTree I),
    finiteDepthKMixture k weights trees →
      riskCurveArea (relevantCoordinates (finiteMixtureMean weights trees))
        (finiteMixtureMean weights trees) ≤ C₀ * (k : ℝ)

def finiteMixtureCompleteAreaBound {I : Type u} [Fintype I]
    (C : ℝ) (k : ℕ) : Prop :=
  ∀ (n : ℕ) (weights : Fin n → ℝ)
    (trees : Fin n → AdaptiveRevealTree I),
    finiteDepthKMixture k weights trees →
      completeAreaMinimum
          (relevantCoordinates (finiteMixtureMean weights trees))
          (finiteMixtureMean weights trees) ≤ C * (k : ℝ)

/-- Claim 61366: after deleting irrelevant coordinates, the separately
optimized endpoint-risk area and the Bellman-optimal complete area satisfy
`S ≤ A ≤ 4 S`; the upper bound is realized by the deterministic cached
`1,2,4,...` dovetail of finite endpoint minimizers, and the campaign-level
risk-curve and complete-area bounds imply one another up to the same factor. -/
def claim61366 : Prop :=
  (∀ {I : Type u} [Fintype I]
    (f : RademacherCube I → ℝ),
    let D := relevantCoordinates f
    let S := riskCurveArea D f
    let A := completeAreaMinimum D f
    targetDeterminedBySet D f ∧
      (∀ π, policyLegalOn D π → policyComplete D f π →
        S ≤ policyArea f π) ∧
      (S ≤ A ∧ A ≤ 4 * S) ∧
        (∀ t, D.card ≤ t → riskCurve D f t = 0) ∧
          (∀ s t, s ≤ t → riskCurve D f t ≤ riskCurve D f s) ∧
            (∀ t, randomizationPurifiesEndpointRisk D f t) ∧
              (∃ π,
                policyLegalOn D π ∧
                  policyComplete D f π ∧
                    policyArea f π = A) ∧
                (∃ policies : ℕ → RevealPolicy I,
                  riskCurveMinimizerFamily D f policies ∧
                    let Q := dovetailPolicy D f policies
                    policyLegalOn D Q ∧
                      policyComplete D f Q ∧
                        (∀ h, Q h = none ↔ targetDeterminedAt f h) ∧
                        (∃ L,
                          firstDyadicPhase D.card L ∧
                            policyArea f Q ≤
                              dyadicPhaseCharge
                                (riskCurve D f) L ∧
                              dyadicPhaseCharge
                                  (riskCurve D f) L ≤ 4 * S ∧
                              (∀ x, ∃ m,
                                m ≤ dyadicRevealBudget L ∧
                                  targetDeterminedAt f
                                    (policyTranscriptAt Q x m))) ∧
                        policyArea f Q ≤ 4 * S ∧
                        A ≤ policyArea f Q)) ∧
  (∀ {I : Type u} [Fintype I] (C₀ : ℝ) (k : ℕ),
    finiteMixtureRiskCurveBound (I := I) C₀ k →
      finiteMixtureCompleteAreaBound (I := I) (4 * C₀) k) ∧
  (∀ {I : Type u} [Fintype I] (C : ℝ) (k : ℕ),
    finiteMixtureCompleteAreaBound (I := I) C k →
      finiteMixtureRiskCurveBound (I := I) C k)

end MathlibPlus.Open.ResearchFormalization.OracleAreaClaim61366
