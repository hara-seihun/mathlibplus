import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755
import MathlibPlus.Open.Research.ScalePackets

open Filter MeasureTheory Set
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0262ScaleMixtures

noncomputable section

/-- The exponential profile used by the Nyman cutoff family. -/
def exponentialCutoffProfile (r : ℝ) : ℝ :=
  Real.exp (-r)

/-- The literal Nyman approximant with exponential cutoff at the scale `N^x`. -/
noncomputable def exponentialNymanCutoffScale
    (N x t : ℝ) : ℝ :=
  MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755.fixedProfileApproximant
    exponentialCutoffProfile (Real.rpow N x) t

/-- The phase contributed by changing the exponential cutoff scale to `N^x`.
The packet below keeps the scale as `N^x` until the claimed scaling identity. -/
noncomputable def exponentialNymanCutoffScalePhase
    (N x y : ℝ) : ℂ :=
  Complex.exp
    (-Complex.I * (Real.log (Real.rpow N x) : ℂ) * (y : ℂ))

/-- The critical-zero residue packet attached to the exponential Nyman cutoff
at the scale `N^x`, before the scale identity is applied. -/
noncomputable def exponentialNymanCutoffPacket
    (ρ : ℂ) (N x y : ℝ) : ℂ :=
  if y = 0 then
    -(1 : ℂ) / ρ
  else
    riemannZeta (ρ + Complex.I * (y : ℂ)) *
        Complex.Gamma (-Complex.I * (y : ℂ)) *
        exponentialNymanCutoffScalePhase N x y /
      ((ρ + Complex.I * (y : ℂ)) * deriv riemannZeta ρ)

/-- The multiplier before it is identified with the zero-extended Fourier
transform. -/
noncomputable def scaleMultiplier
    (N a b : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in Set.Icc a b,
    q x * Complex.exp
      (-Complex.I * (x : ℂ) * (y : ℂ) * (Real.log N : ℂ))

/-- The mixture of the actual exponential-cutoff residue packets. -/
noncomputable def selfSimilarMixturePacket
    (ρ : ℂ) (N a b : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x in Set.Icc a b,
    q x * exponentialNymanCutoffPacket ρ N x y

/-- The squared mass of the mixed packet. -/
noncomputable def selfSimilarMixtureEnergy
    (ρ : ℂ) (N a b : ℝ) (q : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖selfSimilarMixturePacket ρ N a b q y‖ ^ 2

/-- The carrier supplied by the certified simple critical-zero packet:
critical-line location, the displayed removable extension, boundedness,
continuity, and square-integrability. -/
def CertifiedPacketCarrier (ρ : ℂ) : Prop :=
  MathlibPlus.Open.Research.ScalePackets.CertifiedSimpleCriticalZero ρ ∧
    MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ 0 =
      -(1 : ℂ) / ρ ∧
    (∀ y : ℝ, y ≠ 0 →
      MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y =
        riemannZeta (ρ + Complex.I * (y : ℂ)) *
            Complex.Gamma (-Complex.I * (y : ℂ)) /
          ((ρ + Complex.I * (y : ℂ)) * deriv riemannZeta ρ)) ∧
    Continuous (MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ) ∧
    (∃ C : ℝ, ∀ y : ℝ,
      ‖MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y‖ ≤ C) ∧
    Integrable (fun y : ℝ =>
      ‖MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y‖ ^ 2)

/-- Claim 15066: the exponential Nyman cutoff packet at scale `N^x`
acquires the phase `exp(-i*x*y*log N)`, and mixing it with the normalized
zero-extended density gives its Fourier multiplier. -/
def exact_self_similar_scale_multiplier : Prop :=
  ∀ (ρ : ℂ) (a b N : ℝ) (q : ℝ → ℂ),
    CertifiedPacketCarrier ρ →
      MathlibPlus.Open.Research.ScalePackets.IsNormalizedL2Density q a b →
        1 < N →
          (∀ x y : ℝ,
            exponentialNymanCutoffPacket ρ N x y =
              MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y *
                Complex.exp
                  (-Complex.I * (x : ℂ) * (y : ℂ) * (Real.log N : ℂ))) ∧
          (∀ y : ℝ,
            selfSimilarMixturePacket ρ N a b q y =
              MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y *
                scaleMultiplier N a b q y) ∧
          (∀ y : ℝ,
            scaleMultiplier N a b q y =
              MathlibPlus.Open.Research.ScalePackets.qHat q a b
                (y * Real.log N))

/-- Claim 15067: the squared mass of that actual cutoff-packet mixture is
exactly the displayed critical-zero packet-energy integral. -/
def exact_packet_energy_formula : Prop :=
  ∀ (ρ : ℂ) (a b N : ℝ) (q : ℝ → ℂ),
    CertifiedPacketCarrier ρ →
      MathlibPlus.Open.Research.ScalePackets.IsNormalizedL2Density q a b →
        1 < N →
          selfSimilarMixtureEnergy ρ N a b q =
            (1 / (2 * Real.pi)) *
              ∫ y : ℝ,
                ‖MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y‖ ^ 2 *
                  ‖MathlibPlus.Open.Research.ScalePackets.qHat q a b
                    (y * Real.log N)‖ ^ 2

/-- The scalar packet constant in the fixed atomic-array statement. -/
noncomputable def atomicPacketConstant (ρ : ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ,
      ‖MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y‖ ^ 2

/-- The fixed-array packet energy, with complex coefficients and the exact
self-similar phases. -/
noncomputable def atomicPacketEnergy
    (ρ : ℂ) (N : ℝ) (J : ℕ) (x : Fin J → ℝ) (c : Fin J → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ,
      ‖MathlibPlus.Open.Research.ScalePackets.criticalZeroPacket ρ y‖ ^ 2 *
        ‖∑ j : Fin J, c j *
          Complex.exp
            (-Complex.I * (x j : ℂ) * (y : ℂ) * (Real.log N : ℂ))‖ ^ 2

/-- The exact constrained infimum over coefficient vectors of total mass one. -/
noncomputable def atomicPacketMinimumEnergy
    (ρ : ℂ) (N : ℝ) (J : ℕ) (x : Fin J → ℝ) : ℝ :=
  sInf {e : ℝ |
    ∃ c : Fin J → ℂ,
      (∑ j : Fin J, c j) = 1 ∧
        e = atomicPacketEnergy ρ N J x c}

/-- Claim 15073: every fixed distinct atomic array has the positive `Cρ/J`
floor for normalized real or complex coefficients varying with `N`; the
exact constrained minimum and uniform coefficients both approach that value. -/
def fixed_atomic_array_positive_floor : Prop :=
  ∀ (ρ : ℂ) (J : ℕ) (x : Fin J → ℝ),
    CertifiedPacketCarrier ρ →
      0 < J →
        Function.Injective x →
          let Cρ := atomicPacketConstant ρ
          Cρ > 0 ∧
            (∀ c : ℝ → Fin J → ℂ,
              (∀ N : ℝ, ∑ j : Fin J, c N j = 1) →
                Filter.liminf
                    (fun N : ℝ => atomicPacketEnergy ρ N J x (c N))
                    atTop ≥ Cρ / (J : ℝ)) ∧
            Tendsto
              (fun N : ℝ => atomicPacketMinimumEnergy ρ N J x)
              atTop
              (nhds (Cρ / (J : ℝ))) ∧
            Tendsto
              (fun N : ℝ =>
                atomicPacketEnergy ρ N J x
                  (fun _ : Fin J => ((1 / (J : ℝ) : ℝ) : ℂ)))
              atTop
              (nhds (Cρ / (J : ℝ)))

end

end MathlibPlus.Open.ResearchFormalization.O0262ScaleMixtures
