import Mathlib

namespace MathlibPlus.Open.Research.ScalePackets

open Filter
open MeasureTheory

noncomputable section

/-- The analytic content of a certified simple critical zero used by the packet. -/
def CertifiedSimpleCriticalZero (ρ : ℂ) : Prop :=
  ρ.re = (1 / 2 : ℝ) ∧
    riemannZeta ρ = 0 ∧
      deriv riemannZeta ρ ≠ 0 ∧ ρ ≠ 0

/-- The packet formula away from its removable centre. -/
noncomputable def rawCriticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  riemannZeta (ρ + Complex.I * (y : ℂ)) *
      Complex.Gamma (-Complex.I * (y : ℂ)) /
    ((ρ + Complex.I * (y : ℂ)) * deriv riemannZeta ρ)

/-- The normalized packet, with its admitted removable value at zero. -/
noncomputable def criticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  if y = 0 then -(1 : ℂ) / ρ else rawCriticalZeroPacket ρ y

/-- A density on `[a,b]`, represented by its zero extension to the line. -/
noncomputable def zeroExtendedDensity
    (q : ℝ → ℂ) (a b x : ℝ) : ℂ :=
  if x ∈ Set.Icc a b then q x else 0

noncomputable def densityL2NormSq (q : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ x : ℝ, ‖zeroExtendedDensity q a b x‖ ^ 2

/-- Square-integrability and normalization of the zero-extended density. -/
def IsNormalizedL2Density (q : ℝ → ℂ) (a b : ℝ) : Prop :=
  a < b ∧
    AEStronglyMeasurable (zeroExtendedDensity q a b) ∧
      Integrable (fun x : ℝ => ‖zeroExtendedDensity q a b x‖ ^ 2) ∧
        (∫ x : ℝ, zeroExtendedDensity q a b x) = 1

/-- The unnormalized Fourier transform of the zero-extended density. -/
noncomputable def qHat (q : ℝ → ℂ) (a b s : ℝ) : ℂ :=
  ∫ x : ℝ,
    zeroExtendedDensity q a b x *
      Complex.exp (-Complex.I * (x : ℂ) * (s : ℂ))

/-- The exact O-0262 packet energy from the normalized critical-zero packet. -/
noncomputable def packetEnergy
    (ρ : ℂ) (N : ℝ) (q : ℝ → ℂ) (a b : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ,
      ‖criticalZeroPacket ρ y‖ ^ 2 *
        ‖qHat q a b (y * Real.log N)‖ ^ 2

/-- Claim 15068: Plancherel asymptotics for every fixed normalized density. -/
def plancherel_asymptotic_for_fixed_density : Prop :=
  ∀ (a b : ℝ) (ρ : ℂ) (q : ℝ → ℂ),
    CertifiedSimpleCriticalZero ρ →
      IsNormalizedL2Density q a b →
        Tendsto
          (fun N : ℝ => Real.log N * packetEnergy ρ N q a b)
          atTop
          (nhds (densityL2NormSq q a b / ‖ρ‖ ^ 2))

/-- Claim 15069: uniform density minimizes both the L2 and asymptotic constants. -/
def uniform_density_unique_asymptotic_minimizer : Prop :=
  ∀ (a b : ℝ) (ρ : ℂ) (q : ℝ → ℂ),
    IsNormalizedL2Density q a b →
      densityL2NormSq q a b ≥ (1 : ℝ) / (b - a) ∧
        (densityL2NormSq q a b = (1 : ℝ) / (b - a) ↔
          ∀ᵐ x ∂(volume : Measure ℝ),
            x ∈ Set.Icc a b →
              q x = ((1 : ℝ) / (b - a) : ℂ)) ∧
        (CertifiedSimpleCriticalZero ρ →
          Tendsto
              (fun N : ℝ => Real.log N * packetEnergy ρ N q a b)
              atTop
              (nhds (densityL2NormSq q a b / ‖ρ‖ ^ 2)) ∧
            densityL2NormSq q a b / ‖ρ‖ ^ 2 ≥
              (1 : ℝ) / ((b - a) * ‖ρ‖ ^ 2) ∧
            (densityL2NormSq q a b / ‖ρ‖ ^ 2 =
                (1 : ℝ) / ((b - a) * ‖ρ‖ ^ 2) ↔
              ∀ᵐ x ∂(volume : Measure ℝ),
                x ∈ Set.Icc a b →
                  q x = ((1 : ℝ) / (b - a) : ℂ)))

end

end MathlibPlus.Open.Research.ScalePackets
