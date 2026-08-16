import Mathlib

open Filter MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.Claim15070

noncomputable section

/-- The certified simple critical zero carrier used by the admitted packet. -/
def CertifiedSimpleCriticalZero (ρ : ℂ) : Prop :=
  ∃ γ : ℝ,
    ρ = (1 / 2 : ℂ) + (γ : ℂ) * Complex.I ∧
      riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0

/-- The normalized exponential packet, with its removable value at zero. -/
noncomputable def criticalZeroPacket (ρ : ℂ) (y : ℝ) : ℂ :=
  if y = 0 then -(1 : ℂ) / ρ else
    riemannZeta (ρ + Complex.I * (y : ℂ)) *
        Complex.Gamma (-Complex.I * (y : ℂ)) /
      ((ρ + Complex.I * (y : ℂ)) * deriv riemannZeta ρ)

/-- The uniform `[0,1]` scale multiplier before evaluating its closed form. -/
noncomputable def uniformScaleMultiplier (N y : ℝ) : ℂ :=
  ∫ x in Set.Icc (0 : ℝ) 1,
    Complex.exp
      (-Complex.I * (x : ℂ) * (y : ℂ) * (Real.log N : ℂ))

/-- The quotient whose removable value is used by the sinc multiplier. -/
noncomputable def rawUniformSincMultiplier (N y : ℝ) : ℂ :=
  (1 - Complex.exp (-Complex.I * (y : ℂ) * (Real.log N : ℂ))) /
    (Complex.I * (y : ℂ) * (Real.log N : ℂ))

/-- The sinc profile at unit logarithmic scale. -/
noncomputable def uniformSincProfile (t : ℝ) : ℂ :=
  if t = 0 then 1 else
    (1 - Complex.exp (-Complex.I * (t : ℂ))) /
      (Complex.I * (t : ℂ))

/-- The exact uniform-averaging multiplier, extended at its removable point. -/
noncomputable def uniformSincMultiplier (N y : ℝ) : ℂ :=
  if y = 0 then 1 else rawUniformSincMultiplier N y

/-- The packet energy attached to the uniform scale density. -/
noncomputable def uniformPacketEnergy (ρ : ℂ) (N : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ,
      ‖criticalZeroPacket ρ y‖ ^ 2 *
        ‖uniformScaleMultiplier N y‖ ^ 2

/-- Claim 15070: exact uniform sinc multiplier, packet width, and sharp constant. -/
def uniform_averaging_exact_sinc_multiplier : Prop :=
  ∀ ρ : ℂ, CertifiedSimpleCriticalZero ρ →
    (∀ N : ℝ, N > 1 → ∀ y : ℝ,
      uniformScaleMultiplier N y = uniformSincMultiplier N y) ∧
      (∀ N : ℝ, N > 1 → ∀ y : ℝ,
        uniformSincMultiplier N y =
          uniformSincProfile (y * Real.log N)) ∧
      (∀ N : ℝ, N > 1 →
        uniformSincMultiplier N 0 = 1 ∧
          ContinuousAt (uniformSincMultiplier N) 0) ∧
      Tendsto
        (fun N : ℝ => Real.log N * uniformPacketEnergy ρ N)
        atTop
        (nhds (1 / ‖ρ‖ ^ 2))

end

end MathlibPlus.Open.ResearchFormalization.Claim15070
