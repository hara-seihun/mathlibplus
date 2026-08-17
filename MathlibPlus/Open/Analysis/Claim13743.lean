import MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755

open Filter MeasureTheory
open scoped Topology

namespace MathlibPlus.Open.Analysis.Claim13743

noncomputable section

noncomputable def removablePacket
    (ρ : ℂ) (W : ℂ → ℂ) (c γ : ℝ) (t : ℝ) : ℂ :=
  if t = γ then
    -(c : ℂ) * deriv riemannZeta (ρ : ℂ) / ρ
  else
    nymanGammaPacket (ρ : ℂ) W t

/-- Claim 13743: a simple critical zero and a nonzero smooth fixed profile
produce the exact square-integrable nonzero packet, with the removable value
at the zero explicitly retained. -/
def claim13743 : Prop :=
  ∀ (w : ℝ → ℝ) (W : ℂ → ℂ) (c γ : ℝ),
    FormalizationBatchMellin.smoothFixedProfile w →
    w ≠ (fun _ : ℝ => 0) →
    FormalizationBatchMellin13745_13746_13755.profileMellinContinuation
      w W c →
    let ρ : ℂ := (1 / 2 : ℂ) + (γ : ℂ) * Complex.I
    simpleZetaZero ρ →
      MemLp
          (removablePacket ρ W c γ)
          2
          FormalizationBatchMellin.criticalLineMeasure ∧
        (∃ t : ℝ, removablePacket ρ W c γ t ≠ 0) ∧
        (c ≠ 0 →
          removablePacket ρ W c γ γ =
            -(c : ℂ) * deriv riemannZeta ρ / ρ ∧
          Filter.Tendsto
            (nymanGammaPacket ρ W)
            (nhdsWithin γ ({γ} : Set ℝ)ᶜ)
            (𝓝 (-(c : ℂ) * deriv riemannZeta ρ / ρ))) ∧
        (c = 0 → ∃ t : ℝ, removablePacket ρ W c γ t ≠ 0)

end

end MathlibPlus.Open.Analysis.Claim13743
