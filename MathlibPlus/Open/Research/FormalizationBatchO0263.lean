import Mathlib

namespace MathlibPlus.Open.Research.O0263

noncomputable def polyharmonicKappa (k : ℕ) (x : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ ξ : ℝ,
      Complex.exp (-((ξ : ℂ) ^ (2 * k))) *
        Complex.exp (Complex.I * (x : ℂ) * (ξ : ℂ))

noncomputable def polyharmonicKernel (α : ℝ) (k : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ ξ : ℝ,
      Complex.exp (-((α : ℂ) * (ξ : ℂ) ^ (2 * k))) *
        Complex.exp (Complex.I * (t : ℂ) * (ξ : ℂ))

/-- Scaling of the inverse Fourier kernel for the symbol exp (-α ξ^(2k)). -/
def polyharmonicKernelScaling : Prop :=
  ∀ (α : ℝ) (k : ℕ) (t : ℝ), 0 < α → 1 ≤ k →
    polyharmonicKernel α k t =
      (Real.rpow α (-1 / (2 * (k : ℝ))) : ℂ) *
        polyharmonicKappa k (t * Real.rpow α (-1 / (2 * (k : ℝ))))

noncomputable def exponentialEndpointExpectation (k : ℕ) (x : ℝ) : ℝ :=
  ∫ v : ℝ in Set.Ici 0,
    Real.exp (-v) * Real.sin (x * Real.rpow v (1 / (2 * (k : ℝ))))

/-- The exponential-endpoint representation of the polyharmonic kernel. -/
def exactExponentialEndpointRepresentation : Prop :=
  ∀ (x : ℝ) (k : ℕ), 0 < x → 1 ≤ k →
    (Real.pi : ℂ) * (x : ℂ) * polyharmonicKappa k x =
      (exponentialEndpointExpectation k x : ℂ)

end MathlibPlus.Open.Research.O0263
