import Mathlib

namespace MathlibPlus.Open.OracleArea

universe u v

noncomputable section
open scoped BigOperators
open Classical
open MeasureTheory ProbabilityTheory

structure SignedSelector (I : Type*) where
  r : I
  y : I
  z : I
  alpha : ℝ
  beta : ℝ
  epsilon : ℝ

def ValidSignedSelector {I : Type*} (T : SignedSelector I) : Prop :=
  T.r ≠ T.y ∧ T.r ≠ T.z ∧ T.y ≠ T.z ∧
    (T.alpha = -1 ∨ T.alpha = 1) ∧
    (T.beta = -1 ∨ T.beta = 1) ∧
    (T.epsilon = -1 ∨ T.epsilon = 1)

def SelectorValue {I Ω : Type*} (O : I → Ω → ℝ)
    (T : SignedSelector I) (ω : Ω) : ℝ :=
  if T.epsilon * O T.r ω = 1 then T.alpha * O T.y ω else T.beta * O T.z ω

def SelectorSaving {I : Type*} (T : SignedSelector I) (i : I) : ℝ :=
  if i = T.r then 1 else if i = T.y ∨ i = T.z then 3 / 4 else 0

def ConstantBooleanValue (b : Bool) : ℝ := if b then 1 else -1

def SelectorAtom (I : Type*) := SignedSelector I ⊕ Bool

def AtomValue {I Ω : Type*} (O : I → Ω → ℝ) : SelectorAtom I → Ω → ℝ
  | Sum.inl T => SelectorValue O T
  | Sum.inr b => fun _ => ConstantBooleanValue b

def ProbabilityLaw {I : Type*} (Λ : (SelectorAtom I) →₀ ℝ) : Prop :=
  (∀ x, 0 ≤ Λ x) ∧ ∑ x ∈ Λ.support, Λ x = 1

def LawUsesValidSelectors {I : Type*} (Λ : (SelectorAtom I) →₀ ℝ) : Prop :=
  ∀ x ∈ Λ.support,
    match x with
    | Sum.inl T => ValidSignedSelector T
    | Sum.inr _ => True

def SelectorMass {I : Type*} (Λ : (SelectorAtom I) →₀ ℝ) : ℝ :=
  ∑ x ∈ Λ.support, match x with
    | Sum.inl _ => Λ x
    | Sum.inr _ => 0

def SelectorLoad {I : Type*} (Λ : (SelectorAtom I) →₀ ℝ) (i : I) : ℝ :=
  ∑ x ∈ Λ.support, match x with
    | Sum.inl T => Λ x * SelectorSaving T i
    | Sum.inr _ => 0

def MaximumSelectorLoad {I : Type*} (Λ : (SelectorAtom I) →₀ ℝ) : ℝ :=
  sSup (Set.range (SelectorLoad Λ))

def SelectorMixture {I Ω : Type*} (Λ : (SelectorAtom I) →₀ ℝ)
    (O : I → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑ x ∈ Λ.support, Λ x * AtomValue O x ω

def UniformIndependentSigns {I Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (O : I → Ω → ℝ) : Prop :=
  (∀ i, Measurable (O i)) ∧
  (∀ i ω, O i ω = -1 ∨ O i ω = 1) ∧
  (∀ i, μ {ω | O i ω = 1} = (1 : ENNReal) / 2) ∧
  (∀ s : Finset I, ∀ ε : I → ℝ,
    (∀ i ∈ s, ε i = -1 ∨ ε i = 1) →
      μ {ω | ∀ i ∈ s, O i ω = ε i} = ((1 : ENNReal) / 2) ^ s.card)

def AlignedSelectors {I : Type*} (T U : SignedSelector I) : Prop :=
  T.r ≠ U.r ∧ T.y = U.y ∧ T.z = U.z ∧
    T.alpha = U.alpha ∧ T.beta = U.beta ∧ T.epsilon = U.epsilon

def AlignedSelectorOne : SignedSelector (Fin 4) :=
  { r := 0, y := 2, z := 3, alpha := 1, beta := 1, epsilon := 1 }

def AlignedSelectorTwo : SignedSelector (Fin 4) :=
  { r := 1, y := 2, z := 3, alpha := 1, beta := 1, epsilon := 1 }

def AlignedTwoSelectorLaw : SelectorAtom (Fin 4) →₀ ℝ :=
  Finsupp.single (Sum.inl AlignedSelectorOne) (1 / 4) +
    Finsupp.single (Sum.inl AlignedSelectorTwo) (3 / 4)

def SelectorVarianceLoadBound (I Ω : Type*) [Countable I] [MeasurableSpace Ω]
    (μ : Measure Ω) (O : I → Ω → ℝ) : Prop :=
  IsProbabilityMeasure μ → UniformIndependentSigns μ O →
    ∀ Λ : (SelectorAtom I) →₀ ℝ,
      ProbabilityLaw Λ → LawUsesValidSelectors Λ →
      let q := SelectorMass Λ
      let M := MaximumSelectorLoad Λ
      ProbabilityTheory.variance (SelectorMixture Λ O) μ ≤ (7 / 6 : ℝ) * q * M ∧
        (7 / 6 : ℝ) * q * M ≤ (7 / 6 : ℝ) * M

def SelectorVarianceLoadSharpness (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) : Prop :=
  ∀ (O : Fin 4 → Ω → ℝ),
    IsProbabilityMeasure μ → UniformIndependentSigns μ O →
    ProbabilityLaw AlignedTwoSelectorLaw ∧
    LawUsesValidSelectors AlignedTwoSelectorLaw ∧
    AlignedSelectors AlignedSelectorOne AlignedSelectorTwo ∧
    SelectorMass AlignedTwoSelectorLaw = 1 ∧
    MaximumSelectorLoad AlignedTwoSelectorLaw = (3 / 4 : ℝ) ∧
    ProbabilityTheory.variance (SelectorMixture AlignedTwoSelectorLaw O) μ = (13 / 16 : ℝ) ∧
    (∀ c : ℝ, c < 13 / 12 →
      ProbabilityTheory.variance (SelectorMixture AlignedTwoSelectorLaw O) μ >
        c * MaximumSelectorLoad AlignedTwoSelectorLaw)

def SelectorVarianceLoadClaim (I Ω : Type*) [Countable I] [MeasurableSpace Ω]
    (μ : Measure Ω) (O : I → Ω → ℝ) : Prop :=
  SelectorVarianceLoadBound I Ω μ O ∧ SelectorVarianceLoadSharpness Ω μ

end
end MathlibPlus.Open.OracleArea
