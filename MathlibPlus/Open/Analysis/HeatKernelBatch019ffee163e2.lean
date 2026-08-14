import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators Topology
open MeasureTheory
open Filter

/-- The generalized Laguerre polynomial, specified by its standard three-term recurrence. -/
noncomputable def generalizedLaguerre (α : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 1 + α - x
  | n + 2, x =>
      ((((2 * n + 3 : ℕ) : ℝ) + α - x) * generalizedLaguerre α (n + 1) x -
          (((n + 1 : ℕ) : ℝ) + α) * generalizedLaguerre α n x) /
        ((n + 2 : ℕ) : ℝ)

/-- The physicists' Hermite polynomial, specified by its standard recurrence. -/
noncomputable def physicistsHermite : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, y => 2 * y
  | n + 2, y =>
      2 * y * physicistsHermite (n + 1) y -
        2 * ((n + 1 : ℕ) : ℝ) * physicistsHermite n y

noncomputable def heatGaussian (t u : ℝ) : ℝ :=
  (2 * Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(u ^ 2) / (4 * t))

noncomputable def heatKernel (m : ℕ) (t u : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * iteratedDeriv m (fun τ : ℝ => heatGaussian τ u) t

/-- The unnormalised Fourier convention used by the Gaussian identity. -/
noncomputable def unnormalisedFourier (f : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ u : ℝ, (f u : ℂ) * Complex.exp (-Complex.I * (s : ℂ) * (u : ℂ))

/-- Claim 7620: the Gaussian heat-ray kernel has both stated special-function forms
and Fourier transform. -/
def exactGaussianLaguerreHermiteKernel : Prop :=
  ∀ (m : ℕ) (t u s : ℝ), 0 < t →
    unnormalisedFourier (heatKernel m t) s =
        (s : ℂ) ^ (2 * m) * Complex.exp (-(t : ℂ) * (s : ℂ) ^ 2) ∧
      heatKernel m t u =
        (m.factorial : ℝ) /
            (2 * Real.sqrt Real.pi * Real.rpow t ((m : ℝ) + (1 / 2 : ℝ))) *
          Real.exp (-(u ^ 2) / (4 * t)) *
            generalizedLaguerre (-1 / 2 : ℝ) m ((u ^ 2) / (4 * t)) ∧
      let y : ℝ := u / (2 * Real.sqrt t)
      heatKernel m t u =
        (-1 : ℝ) ^ m /
            (2 * Real.sqrt Real.pi * (4 : ℝ) ^ m *
              Real.rpow t ((m : ℝ) + (1 / 2 : ℝ))) *
          Real.exp (-(y ^ 2)) * physicistsHermite (2 * m) y

/-- The Gamma density on the nonnegative half-line. -/
noncomputable def gammaDensity (shape rate y : ℝ) : ℝ :=
  if 0 ≤ y then
    Real.rpow rate shape / Real.Gamma shape *
        Real.rpow y (shape - 1) * Real.exp (-rate * y)
  else 0

noncomputable def gammaMeasure (shape rate : ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (gammaDensity shape rate y))

/-- Density of the nonnegative square root of a Gamma variable with shape
`m + 1/2` and rate `m/q`. -/
noncomputable def positiveSqrtGammaDensity (m : ℕ) (q s : ℝ) : ℝ :=
  if 0 ≤ s then
    (2 * Real.rpow ((m : ℝ) / q) ((m : ℝ) + (1 / 2 : ℝ)) /
        Real.Gamma ((m : ℝ) + (1 / 2 : ℝ))) *
      Real.rpow s (2 * (m : ℝ)) * Real.exp (-((m : ℝ) / q) * s ^ 2)
  else 0

noncomputable def positiveSqrtGammaMeasure (m : ℕ) (q : ℝ) : Measure ℝ :=
  volume.withDensity (fun s => ENNReal.ofReal (positiveSqrtGammaDensity m q s))

noncomputable def positiveSqrtGammaCosineExpectation
    (m : ℕ) (q u : ℝ) : ℝ :=
  ∫ s : ℝ, Real.cos (u * s) ∂positiveSqrtGammaMeasure m q

/-- Claim 7621: the heat-ray value, its large-order asymptotic, and the
Gamma-square representation of the normalized kernel. -/
def heatRayKernelNormalization : Prop :=
  (∀ (m : ℕ) (q u : ℝ), 0 < m → 0 < q →
    IsProbabilityMeasure (positiveSqrtGammaMeasure m q) ∧
      Measure.map (fun s : ℝ => s ^ 2) (positiveSqrtGammaMeasure m q) =
        gammaMeasure ((m : ℝ) + (1 / 2 : ℝ)) ((m : ℝ) / q) ∧
      heatKernel m ((m : ℝ) / q) 0 =
          Real.Gamma ((m : ℝ) + (1 / 2 : ℝ)) / (2 * Real.pi) *
            Real.rpow (q / (m : ℝ)) ((m : ℝ) + (1 / 2 : ℝ)) ∧
        heatKernel m ((m : ℝ) / q) u /
            heatKernel m ((m : ℝ) / q) 0 =
          positiveSqrtGammaCosineExpectation m q u) ∧
  (∀ q : ℝ, 0 < q →
    Tendsto
        (fun m : ℕ =>
          if 0 < m then
            heatKernel m ((m : ℝ) / q) 0 /
                (Real.sqrt (q / (2 * Real.pi * (m : ℝ))) *
                  (q / Real.exp 1) ^ m)
          else 1)
        atTop (𝓝 1) ∧
      ∀ u : ℝ,
        Tendsto
          (fun m : ℕ =>
            if 0 < m then
              heatKernel m ((m : ℝ) / q) u /
                  heatKernel m ((m : ℝ) / q) 0
            else 0)
          atTop (𝓝 (Real.cos (Real.sqrt q * u))))

end MathlibPlus.Open.Analysis
