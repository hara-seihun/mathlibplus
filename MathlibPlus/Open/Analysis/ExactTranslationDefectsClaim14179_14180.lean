import Mathlib
import MathlibPlus.Open.Analysis.ExplicitLongWavePacketClaim14178

open MeasureTheory

namespace MathlibPlus.Open.Analysis

/-- Exact overlap and squared defect of the admitted long-wave packet on complex `L²(ℝ)`. -/
def exactPacketDefect_claim14179 : Prop :=
  ∀ (a θ r : ℝ) (z : ℂ) (R : ℝ),
    a ≠ 0 →
    0 ≤ r →
    z = (r : ℂ) * Complex.exp (Complex.I * θ) →
    R > |a| / 2 →
    ∀ (τ : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure ℝ)),
      (∀ f : Lp ℂ 2 (volume : Measure ℝ),
        (τ f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + a)) →
      ∃ f_R : Lp ℂ 2 (volume : Measure ℝ),
        (∀ᵐ x ∂(volume : Measure ℝ),
          (f_R : ℝ → ℂ) x =
            ((Real.rpow (2 * R) (-1 / 2 : ℝ)) : ℂ) *
              Complex.exp (Complex.I * (θ * x / a)) *
                Set.indicator (Set.Icc (-R) R) (fun _ : ℝ => (1 : ℂ)) x) ∧
          ‖f_R‖ = 1 ∧
          volume
              (Set.Icc (-R) R ∩
                (fun x : ℝ => x + a) ⁻¹' Set.Icc (-R) R) =
            ENNReal.ofReal (2 * R - |a|) ∧
          ‖τ f_R - z • f_R‖ ^ 2 = (r - 1) ^ 2 + |a| * r / R

/-- The exact scalar defect infimum for the admitted translation representation. -/
def exactOptimalScalarDefect_claim14180 : Prop :=
  ∀ (a : ℝ) (z : ℂ),
    a ≠ 0 →
    ∀ (τ : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure ℝ)),
      (∀ f : Lp ℂ 2 (volume : Measure ℝ),
        (τ f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + a)) →
      sInf
          {d : ℝ |
            ∃ f : Lp ℂ 2 (volume : Measure ℝ),
              ‖f‖ = 1 ∧ d = ‖τ f - z • f‖} =
        |‖z‖ - 1|

end MathlibPlus.Open.Analysis
