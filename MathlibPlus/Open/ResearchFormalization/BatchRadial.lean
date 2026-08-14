import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

namespace MathlibPlus.Open.ResearchFormalization.BatchRadial

noncomputable section

abbrev L2Interval := MeasureTheory.Lp ℝ 2 (volume.restrict (Set.Ioo (0 : ℝ) 1))
abbrev L2Line := MeasureTheory.Lp ℝ 2 (volume : Measure ℝ)

def evenSupported (radius : ℝ) (g : L2Line) : Prop :=
  (∀ᵐ x ∂(volume : Measure ℝ), g (-x) = g x) ∧
    (∀ᵐ x ∂(volume : Measure ℝ), radius ≤ |x| → g x = 0)

def extensionFormula (f : L2Interval) (x : ℝ) : ℝ :=
  if |x| < 1 then (Real.sqrt 2)⁻¹ * f |x| else 0

def radialExtensionProperty (U : L2Interval →L[ℝ] L2Line) : Prop :=
  (∀ f, ∀ᵐ x ∂(volume : Measure ℝ), U f x = extensionFormula f x) ∧
    (∀ f, ‖U f‖ = ‖f‖) ∧
    (∀ f, evenSupported 1 (U f)) ∧
    (∀ f g, U f = U g → f = g) ∧
    (∀ g, evenSupported 1 g → ∃ f, U f = g)

def translationProperty (a : ℝ) (T : L2Line →L[ℝ] L2Line) : Prop :=
  ∀ h, ∀ᵐ x ∂(volume : Measure ℝ), T h x = h (x + a)

def compressedOperator (U : L2Interval →L[ℝ] L2Line)
    (τ : ℝ → L2Line →L[ℝ] L2Line) (a : ℝ) :
    L2Interval →L[ℝ] L2Interval :=
  (ContinuousLinearMap.adjoint U).comp ((τ a + τ (-a)).comp U)

def radialCompressionData (U : L2Interval →L[ℝ] L2Line)
    (τ : ℝ → L2Line →L[ℝ] L2Line)
    (C : ℝ → L2Interval →L[ℝ] L2Interval) : Prop :=
  radialExtensionProperty U ∧
    (∀ a, translationProperty a (τ a)) ∧
    (∀ a, 0 ≤ a → C a = compressedOperator U τ a)

def claim10338 : Prop :=
  ∃ U : L2Interval →L[ℝ] L2Line, radialExtensionProperty U

def claim10339 : Prop :=
  ∃ (U : L2Interval →L[ℝ] L2Line)
    (τ : ℝ → L2Line →L[ℝ] L2Line)
    (C : ℝ → L2Interval →L[ℝ] L2Interval),
    radialCompressionData U τ C

def radialAutocorrelation (U : L2Interval →L[ℝ] L2Line)
    (f : L2Interval) (a : ℝ) : ℝ :=
  ∫ x : ℝ, U f (x + a) * U f x

def claim10340 : Prop :=
  ∃ (U : L2Interval →L[ℝ] L2Line)
    (τ : ℝ → L2Line →L[ℝ] L2Line)
    (C : ℝ → L2Interval →L[ℝ] L2Interval),
    radialCompressionData U τ C ∧
      (∀ f a, 0 ≤ a →
        inner ℝ f (C a f) = (2 : ℝ) * radialAutocorrelation U f a)

def claim10341 : Prop :=
  ∃ (U : L2Interval →L[ℝ] L2Line)
    (τ : ℝ → L2Line →L[ℝ] L2Line)
    (C : ℝ → L2Interval →L[ℝ] L2Interval),
    radialCompressionData U τ C ∧
      (∀ a, 2 ≤ a → C a = 0)

def scaledTest (U : L2Interval →L[ℝ] L2Line) (t : ℝ)
    (f : L2Interval) (u : ℝ) : ℝ :=
  Real.sqrt (t / 2) * U f (t * u / 2)

def radialDilationProperty (t : ℝ)
    (U : L2Interval →L[ℝ] L2Line)
    (Φ : L2Interval →L[ℝ] L2Line) : Prop :=
  (∀ f, ∀ᵐ u ∂(volume : Measure ℝ),
    Φ f u = scaledTest U t f u) ∧
    (∀ f, ‖Φ f‖ = ‖f‖) ∧
    (∀ f, evenSupported (2 / t) (Φ f)) ∧
    (∀ f g, Φ f = Φ g → f = g) ∧
    (∀ g, evenSupported (2 / t) g → ∃ f, Φ f = g)

def claim10342 : Prop :=
  ∀ t, 0 < t →
    ∃ (U : L2Interval →L[ℝ] L2Line) (Φ : L2Interval →L[ℝ] L2Line),
      radialExtensionProperty U ∧ radialDilationProperty t U Φ

def dilatedAutocorrelation (U : L2Interval →L[ℝ] L2Line)
    (t : ℝ) (f : L2Interval) (u : ℝ) : ℝ :=
  ∫ x : ℝ, scaledTest U t f (x + u) * scaledTest U t f x

def claim10343 : Prop :=
  ∀ (U : L2Interval →L[ℝ] L2Line), radialExtensionProperty U →
    ∀ t, 0 < t → ∀ f,
      (∀ u, dilatedAutocorrelation U t f u =
        radialAutocorrelation U f (t * u / 2)) ∧
      (∀ u, 4 / t ≤ |u| → dilatedAutocorrelation U t f u = 0)

def restrictionFormula (q Q : ℝ) (f : L2Interval) (x : ℝ) : ℝ :=
  Real.sqrt (Q / q) * f (Q * x / q) *
    if x ∈ Set.Ioo (0 : ℝ) (q / Q) then 1 else 0

def restrictionProperty (q Q : ℝ)
    (J : L2Interval →L[ℝ] L2Interval) : Prop :=
  (∀ f, ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
    J f x = restrictionFormula q Q f x) ∧
    (∀ f, ‖J f‖ = ‖f‖)

def claim10356 : Prop :=
  ∀ q Q, 0 < q → q ≤ Q →
    ∃ (U : L2Interval →L[ℝ] L2Line)
      (J : L2Interval →L[ℝ] L2Interval),
      radialExtensionProperty U ∧ restrictionProperty q Q J ∧
        (∀ f, ∀ᵐ u ∂(volume : Measure ℝ),
          scaledTest U (4 / Q) (J f) u = scaledTest U (4 / q) f u)

end
end MathlibPlus.Open.ResearchFormalization.BatchRadial
