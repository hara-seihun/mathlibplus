import MathlibPlus.Open.Probability.DepthTwoOracleSharpFiveFour

namespace MathlibPlus.Open.Probability.ResearchFormalization61098

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

abbrev BooleanFunction (I : Type*) := (I → Sign) → Sign

/-- The law has at most the two Boolean atoms named in the source claim. -/
def supportedOnAtMostTwo
    {I : Type*} (Λ : FiniteProbabilityLaw (BooleanFunction I)) : Prop :=
  ∃ T U : BooleanFunction I,
    ∀ V, V ∈ Λ.support → V = T ∨ V = U

/-- Every atom in the law is computed by a deterministic tree of depth at most
 two; no monotonicity condition is added. -/
def hasDepthAtMostTwo
    {I : Type*} (Λ : FiniteProbabilityLaw (BooleanFunction I)) : Prop :=
  ∀ V, V ∈ Λ.support →
    ∃ tree : SignDecisionTree I,
      tree.depth ≤ 2 ∧ tree.evaluate = V

/-- The ternary transcript records unrevealed coordinates by `0` and the two
signs by `1` and `2`. -/
def signCode (s : Sign) : Fin 3 :=
  if s = 0 then 1 else 2

abbrev RevealTranscript (I : Type*) := I →₀ Fin 3

def transcriptCell
    {I Ω : Type*} (O : I → Ω → Sign)
    (h : RevealTranscript I) : Set Ω :=
  {ω | ∀ i, h i ≠ 0 → h i = signCode (O i ω)}

def constantOnCell {Ω : Type*} (f : Ω → ℝ) (C : Set Ω) : Prop :=
  ∀ ⦃ω ω' : Ω⦄, ω ∈ C → ω' ∈ C → f ω = f ω'

noncomputable def conditionalMeanOnCell
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else (∫ ω in C, f ω ∂P) / (P C).toReal

noncomputable def conditionalVarianceOnCell
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  if P C = 0 then 0 else
    (∫ ω in C, (f ω - conditionalMeanOnCell P f C) ^ 2 ∂P) /
      (P C).toReal

/-- The posterior variance is zero on a cell on which the target is already
measurable. -/
noncomputable def posteriorVarianceOnCell
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (C : Set Ω) : ℝ :=
  @ite ℝ (constantOnCell f C) (Classical.propDecidable _) 0
    (conditionalVarianceOnCell P f C)

/-- One adaptive reveal, with immediate stopping on a measurable cell. -/
noncomputable def adaptiveStep
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I)
    (h : RevealTranscript I) (ω : Ω) : RevealTranscript I :=
  @ite (RevealTranscript I)
    (constantOnCell (mixtureMean Λ O) (transcriptCell O h))
    (Classical.propDecidable _) h
    (match policy h with
     | none => h
     | some i => h.update i (signCode (O i ω)))

/-- The transcript after `m` applications of the adaptive policy. -/
noncomputable def adaptiveTranscript
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I) :
    ℕ → Ω → RevealTranscript I
  | 0, _ => 0
  | m + 1, ω =>
      adaptiveStep Λ O policy
        (adaptiveTranscript Λ O policy m ω) ω

/-- A legal policy only reveals a coordinate that is absent from the current
transcript. -/
def legalAdaptivePolicy
    {I : Type*}
    (policy : RevealTranscript I → Option I) : Prop :=
  ∀ h i, policy h = some i → h i = 0

/-- The policy stops exactly when the mixture mean is measurable on the current
transcript cell. -/
def policyStopsExactly
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I) : Prop :=
  (∀ h,
    constantOnCell (mixtureMean Λ O) (transcriptCell O h) →
      policy h = none) ∧
  (∀ h,
    ¬ constantOnCell (mixtureMean Λ O) (transcriptCell O h) →
      ∃ i, policy h = some i ∧ h i = 0)

/-- Every sample path reaches a measurable target cell. -/
def eventuallyStops
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I) : Prop :=
  ∀ ω, ∃ m,
    constantOnCell (mixtureMean Λ O)
      (transcriptCell O (adaptiveTranscript Λ O policy m ω))

/-- One root-inclusive posterior-variance term. -/
noncomputable def posteriorVarianceTerm
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (P : Measure Ω) (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I) (m : ℕ) : ℝ :=
  ∫ ω,
    posteriorVarianceOnCell P (mixtureMean Λ O)
      (transcriptCell O (adaptiveTranscript Λ O policy m ω)) ∂P

/-- Root-inclusive cumulative posterior variance, with its real tsum guarded by
an explicit summability predicate below. -/
noncomputable def posteriorVarianceArea
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (P : Measure Ω) (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I) : ℝ :=
  ∑' m : ℕ, posteriorVarianceTerm Λ P O policy m

def posteriorVarianceAreaSummable
    {I Ω : Type*} [MeasurableSpace Ω]
    (Λ : FiniteProbabilityLaw (BooleanFunction I))
    (P : Measure Ω) (O : I → Ω → Sign)
    (policy : RevealTranscript I → Option I) : Prop :=
  Summable (posteriorVarianceTerm Λ P O policy)

/-- The sign-valued parity of two independent coordinates. -/
def twoCoordinateParity : BooleanFunction (Fin 2) :=
  fun x => if x 0 = x 1 then 1 else 0

/-- Sharpness is stated on an actual four-point probability carrier and for
all legal policies with the same stopping and summability semantics. -/
def paritySharpness : Prop :=
  ∃ (Ω : Type) (mΩ : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := mΩ
    ∃ (fΩ : Fintype Ω),
      letI : Fintype Ω := fΩ
      ∃ (P : Measure Ω) (hP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := hP
        ∃ (O : Fin 2 → Ω → Sign),
          Fintype.card Ω = 4 ∧
            uniformIndependentSigns P O ∧
            hasDepthAtMostTwo (pointMass twoCoordinateParity) ∧
            (∀ policy : RevealTranscript (Fin 2) → Option (Fin 2),
              legalAdaptivePolicy policy →
                policyStopsExactly (pointMass twoCoordinateParity) O policy →
                  eventuallyStops (pointMass twoCoordinateParity) O policy →
                    posteriorVarianceAreaSummable
                      (pointMass twoCoordinateParity) P O policy →
                      (2 : ℝ) ≤
                        posteriorVarianceArea
                          (pointMass twoCoordinateParity) P O policy) ∧
            (∃ policy : RevealTranscript (Fin 2) → Option (Fin 2),
              legalAdaptivePolicy policy ∧
                policyStopsExactly (pointMass twoCoordinateParity) O policy ∧
                eventuallyStops (pointMass twoCoordinateParity) O policy ∧
                posteriorVarianceAreaSummable
                  (pointMass twoCoordinateParity) P O policy ∧
                posteriorVarianceArea
                  (pointMass twoCoordinateParity) P O policy = 2)

/-- Claim 61098: every finite-or-countable two-atom depth-two mixture has a
legal adaptive coordinate-reveal policy, stopped exactly when its mixture mean
is measurable, with root-inclusive cumulative posterior variance at most two;
the constant is sharp for a two-coordinate parity. -/
def claim61098 : Prop :=
  (∀ (I Ω : Type*) [Countable I] [MeasurableSpace Ω]
      (Λ : FiniteProbabilityLaw (BooleanFunction I))
      (P : Measure Ω) [IsProbabilityMeasure P]
      (O : I → Ω → Sign),
      uniformIndependentSigns P O →
        supportedOnAtMostTwo Λ →
          hasDepthAtMostTwo Λ →
            ∃ policy : RevealTranscript I → Option I,
              legalAdaptivePolicy policy ∧
                policyStopsExactly Λ O policy ∧
                eventuallyStops Λ O policy ∧
                posteriorVarianceAreaSummable Λ P O policy ∧
                posteriorVarianceArea Λ P O policy ≤ 2) ∧
    paritySharpness

end

end MathlibPlus.Open.Probability.ResearchFormalization61098
