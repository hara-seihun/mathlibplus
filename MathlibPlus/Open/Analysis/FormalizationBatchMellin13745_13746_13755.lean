import Mathlib
import MathlibPlus.Open.Analysis.FormalizationBatchMellin
import MathlibPlus.Open.Analysis.ResearchFormalizationBatch13764_13765
import MathlibPlus.Open.Research.ExponentialMellinBergmanFormalization_01a00b5c7b35

open scoped BigOperators ComplexConjugate ENNReal
open Filter MeasureTheory Set Topology

namespace MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755

noncomputable section

abbrev PositiveReal := {x : ℝ // 0 < x}
abbrev PositiveNat := {n : ℕ // 0 < n}
abbrev nymanHMeasure : Measure ℝ :=
  MathlibPlus.Open.Research.ExponentialMellinBergman.hMeasure
abbrev criticalMeasure : Measure ℝ :=
  MathlibPlus.Open.Analysis.FormalizationBatchMellin.criticalLineMeasure

/-- The fixed-profile Nyman approximant at the positive scale `N`. -/
noncomputable def fixedProfileApproximant (w : ℝ → ℝ) (N t : ℝ) : ℝ :=
  ∑' n : PositiveNat,
    MathlibPlus.Open.Research.ExponentialMellinBergman.moebiusReal n.1 *
      w ((n.1 : ℝ) / N) *
      MathlibPlus.Open.Research.ExponentialMellinBergman.gamma n.1 t

/-- The weighted `L²([1,∞),dt/t²)` error norm. -/
noncomputable def hDistance (f g : ℝ → ℝ) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ => f t - g t) (2 : ℝ≥0∞) nymanHMeasure

/-- The critical-line `L²(dt/(2π))` norm of a Mellin packet. -/
noncomputable def criticalPacketNorm (K : ℝ → ℂ) : ℝ≥0∞ :=
  eLpNorm K (2 : ℝ≥0∞) criticalMeasure

noncomputable def profileLowerBound (ρ : ℂ) (W : ℂ → ℂ) : ℝ≥0∞ :=
  criticalPacketNorm
      (MathlibPlus.Open.Analysis.nymanGammaPacket ρ W) /
    ENNReal.ofReal ‖deriv riemannZeta ρ‖

/-- A simple zero on the critical line, in the carrier used by the packet. -/
def criticalLineSimpleZero (ρ : ℂ) : Prop :=
  ∃ γ : ℝ,
    ρ = (1 / 2 : ℂ) + (γ : ℂ) * Complex.I ∧
      MathlibPlus.Open.Analysis.simpleZetaZero ρ

noncomputable def realErrorLimsup (w : ℝ → ℝ) : ℝ≥0∞ :=
  Filter.limsup
    (fun N : PositiveReal =>
      hDistance
        (fixedProfileApproximant w (N.1 : ℝ))
        (fun _ : ℝ => 1))
    atTop

noncomputable def integerErrorLimsup (w : ℝ → ℝ) : ℝ≥0∞ :=
  Filter.limsup
    (fun N : PositiveNat =>
      hDistance
        (fixedProfileApproximant w (N.1 : ℝ))
        (fun _ : ℝ => 1))
    atTop

/-- The Mellin continuation data of a smooth fixed profile. -/
def profileMellinContinuation (w : ℝ → ℝ) (W : ℂ → ℂ) (c : ℝ) : Prop :=
  (∀ z : ℂ, 0 < z.re →
    W z = MathlibPlus.Open.Analysis.FormalizationBatchMellin.realMellin w z) ∧
  (∃ η : ℝ, 0 < η ∧
    MeromorphicOn W {z : ℂ | -η < z.re} ∧
      ∃ V : ℂ → ℂ,
        AnalyticOnNhd ℂ V {z : ℂ | -η < z.re} ∧
        (∀ z : ℂ, -η < z.re → z ≠ 0 →
          W z = (c : ℂ) * Complex.Gamma z + V z) ∧
        (∀ a b : ℝ, -η < a → a ≤ b →
          ∀ m : ℕ, ∃ C T : ℝ, 0 ≤ C ∧ 0 ≤ T ∧
            ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T ≤ |t| →
              ‖V ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
                C * Real.rpow (1 + |t|) (-(m : ℝ))) ∧
        Filter.Tendsto (fun z : ℂ => z * W z)
          (nhdsWithin 0 (({0} : Set ℂ)ᶜ)) (𝓝 (c : ℂ)))

/-- A smooth compactly supported Mellin test packet on the positive half-line. -/
def smoothCompactMellinTest (h : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ h ∧
    HasCompactSupport h ∧
    Function.support h ⊆ Set.Ioi (0 : ℝ)

/-- The exact main-packet coefficient from the logarithmic scale-Abel transform. -/
noncomputable def profileCoefficient
    (ρ : ℂ) (W : ℂ → ℂ) (h : ℝ → ℂ) (lam : ℝ) : ℂ :=
  ∫ t : ℝ,
    let s : ℂ := (1 / 2 : ℂ) + Complex.I * (t : ℂ)
    riemannZeta s * W (ρ + (lam : ℂ) - s) *
        star (MathlibPlus.Open.Analysis.FormalizationBatchMellin.criticalLineMellin h t) / s
    ∂criticalMeasure

/-- Exponentially damped Möbius approximants do not converge to one. -/
def claim_13745 : Prop :=
  ∃ ρ : ℂ,
    criticalLineSimpleZero ρ ∧
      let w : ℝ → ℝ := fun r => Real.exp (-r)
      let error : PositiveNat → ℝ≥0∞ := fun N =>
        hDistance
          (fixedProfileApproximant w (N.1 : ℝ))
          (fun _ : ℝ => 1)
      let B : ℝ≥0∞ := profileLowerBound ρ Complex.Gamma
      ¬ Tendsto error atTop (𝓝 0) ∧
        0 < B ∧
        B ≤ Filter.limsup error atTop

/-- Uniform real-to-integer transfer for every smooth fixed profile. -/
def claim_13746 : Prop :=
  ∀ w : ℝ → ℝ,
    MathlibPlus.Open.Analysis.FormalizationBatchMellin.smoothFixedProfile w →
    (∃ C N₀ : ℝ, 0 ≤ C ∧ 0 < N₀ ∧
      ∀ N : ℝ, N₀ ≤ N →
        ∀ u : ℝ, 0 < u → |u - N| ≤ 1 →
          hDistance
              (fixedProfileApproximant w u)
              (fixedProfileApproximant w N) ≤
            ENNReal.ofReal (C / Real.sqrt N)) ∧
    (∀ ρ : ℂ, ∀ W : ℂ → ℂ, ∀ c : ℝ,
      criticalLineSimpleZero ρ →
      w ≠ (fun _ : ℝ => 0) →
      profileMellinContinuation w W c →
      realErrorLimsup w = integerErrorLimsup w ∧
        (profileLowerBound ρ W ≤ realErrorLimsup w ↔
          profileLowerBound ρ W ≤ integerErrorLimsup w))

/-- The main Abel packet has a removable profile singularity. -/
def claim_13755 : Prop :=
  ∀ (w : ℝ → ℝ) (W : ℂ → ℂ) (c : ℝ) (ρ : ℂ) (h : ℝ → ℂ),
    MathlibPlus.Open.Analysis.FormalizationBatchMellin.smoothFixedProfile w →
    profileMellinContinuation w W c →
    criticalLineSimpleZero ρ →
    smoothCompactMellinTest h →
    Filter.Tendsto (fun lam : ℝ => profileCoefficient ρ W h lam)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (profileCoefficient ρ W h 0)) ∧
    Filter.Tendsto (fun s : ℂ =>
        riemannZeta s * W (ρ - s) / s)
      (nhdsWithin ρ (({ρ} : Set ℂ)ᶜ))
      (𝓝 (-(c : ℂ) * deriv riemannZeta ρ / ρ))

end
end MathlibPlus.Open.Analysis.FormalizationBatchMellin13745_13746_13755
