import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def bilateralLaplace (h : ℝ → ℝ) (spectral : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (spectral * (x : ℂ)) * (h x : ℂ)

noncomputable def decayingMode (h : ℝ → ℝ) (spectral : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-spectral * (x : ℂ)) *
    ∫ t : ℝ in Set.Iic x, Complex.exp (spectral * (t : ℂ)) * (h t : ℂ)

noncomputable def gaugedMode (h : ℝ → ℝ) (φ : ℝ → ℝ) (spectral : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (((φ x : ℂ) + spectral * (x : ℂ)) / 2) * decayingMode h spectral x

def rapidlyDecreasing (h : ℝ → ℝ) : Prop :=
  ∀ n : ℕ,
    Filter.Tendsto (fun x : ℝ => |x| ^ n * |h x|) (Filter.cocompact ℝ) (nhds 0)

def exactAppellParityModeTransport : Prop :=
  ∀ (h φ : ℝ → ℝ) (spectral : ℂ),
    rapidlyDecreasing h →
    (∀ x : ℝ, h (-x) = h x) →
    (∀ x : ℝ, h x = Real.exp (-(φ x))) →
    MeasureTheory.Integrable
      (fun t : ℝ => Complex.exp (spectral * (t : ℂ)) * (h t : ℂ)) →
    bilateralLaplace h spectral = 0 →
    bilateralLaplace h (-spectral) = 0 ∧
      ∀ x : ℝ, gaugedMode h φ spectral (-x) = -gaugedMode h φ (-spectral) x

def exactHermitianModeTransport : Prop :=
  ∀ (h φ : ℝ → ℝ) (spectral : ℂ),
    rapidlyDecreasing h →
    (∀ x : ℝ, h (-x) = h x) →
    (∀ x : ℝ, h x = Real.exp (-(φ x))) →
    MeasureTheory.Integrable
      (fun t : ℝ => Complex.exp (spectral * (t : ℂ)) * (h t : ℂ)) →
    bilateralLaplace h spectral = 0 →
    ∀ x : ℝ, star (gaugedMode h φ spectral x) = gaugedMode h φ (star spectral) x

end MathlibPlus.Open.Analysis
