import Mathlib

namespace MathlibPlus.Open.Analysis

open MeasureTheory

noncomputable section

abbrev L2Real := MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

def l2Rep (f : L2Real) : ℝ → ℂ := (↑(↑f) : ℝ → ℂ)

def shiftedGammaC (μ : ℝ) (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma ((μ : ℂ) + s / 2)

def shiftedGammaCReal (μ s : ℝ) : ℝ :=
  Real.pi ^ (-s / 2) * Real.Gamma (μ + s / 2)

def shiftedGammaKernel (μ σ u : ℝ) : ℝ :=
  2 * Real.pi ^ μ * Real.exp ((2 * μ + σ) * u - Real.pi * Real.exp (2 * u))

def noTwoPiFourierIntegral (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-Complex.I * (t * x)) * f x ∂(volume : Measure ℝ)

def IsNoTwoPiFourier (F : L2Real →L[ℂ] L2Real) : Prop :=
  ∀ f : SchwartzMap ℝ ℂ,
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      l2Rep (F ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) f)) t =
        noTwoPiFourierIntegral (f : ℝ → ℂ) t

def shiftedGammaConvolution (μ σ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f y * (shiftedGammaKernel μ σ (x - y) : ℂ) ∂(volume : Measure ℝ)

def IsConvolutionBy (μ σ : ℝ) (G : L2Real →L[ℂ] L2Real) : Prop :=
  ∀ f : L2Real,
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      l2Rep (G f) x = shiftedGammaConvolution μ σ (l2Rep f) x

def shiftedGammaMultiplier (μ σ t : ℝ) : ℂ :=
  shiftedGammaC μ ((σ : ℂ) - (t : ℂ) * Complex.I)

def IsFourierMultiplier (μ σ : ℝ) (F G : L2Real →L[ℂ] L2Real) : Prop :=
  ∀ f : L2Real,
    ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      l2Rep (F (G f)) t =
        shiftedGammaMultiplier μ σ t * l2Rep (F f) t

def shiftedGammaQuotientInL2 (μ σ : ℝ) (F : L2Real →L[ℂ] L2Real) (h : L2Real) : Prop :=
  let q := fun t : ℝ => l2Rep (F h) t / shiftedGammaMultiplier μ σ t
  AEStronglyMeasurable q (volume : Measure ℝ) ∧ eLpNorm q 2 (volume : Measure ℝ) < ⊤

def IsFredholmL2 (G : L2Real →L[ℂ] L2Real) : Prop :=
  FiniteDimensional ℂ (LinearMap.ker G.toLinearMap) ∧
    IsClosed (Set.range (fun f : L2Real => G f)) ∧
    FiniteDimensional ℂ (L2Real ⧸ LinearMap.range G.toLinearMap)

def convolutionOperatorGeometry_claim6971 : Prop :=
  ∀ μ σ : ℝ, 0 < μ + σ / 2 →
    ∃ (F G : L2Real →L[ℂ] L2Real),
      IsNoTwoPiFourier F ∧
        IsConvolutionBy μ σ G ∧
        IsFourierMultiplier μ σ F G ∧
        IsBoundedLinearMap ℂ (G : L2Real → L2Real) ∧
        IsStarNormal G ∧
        ‖G‖ = shiftedGammaCReal μ σ ∧
        Function.Injective G ∧
        Set.range (fun f : L2Real => G f) =
          {h : L2Real | shiftedGammaQuotientInL2 μ σ F h} ∧
        Dense (Set.range (fun f : L2Real => G f)) ∧
        Set.range (fun f : L2Real => G f) ≠ Set.univ ∧
        ¬IsClosed (Set.range (fun f : L2Real => G f)) ∧
        ¬IsCompactOperator (G : L2Real → L2Real) ∧
        ¬IsFredholmL2 G

end

end MathlibPlus.Open.Analysis
