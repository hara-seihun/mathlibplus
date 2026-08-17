import Mathlib
import MathlibPlus.Open.ResearchFormalization.O0356.FirstPairExteriorSquare15677

open Filter Asymptotics
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0356.Claim15678

noncomputable section

open MathlibPlus.Open.ResearchFormalization.O0356.Claim15677

/-- Claim 15678: the factorial-normalized first conjugate-pair shell has the
stated positive-infinity multiplicative asymptotic, inverse-square-root
magnitude with nonzero coefficient, and eventual negative real sign. -/
def claim15678_normalizedFirstPairAsymptotic : Prop :=
  ∀ (S_f : ℕ → ℂ) (ρ₁ : ℂ) (γ₁ : ℝ),
    IsHadamardLiCoefficientSequence S_f →
      MathlibPlus.Open.ResearchFormalization.O0356.Claim15677.RiemannHypothesis →
        FirstPositiveNontrivialZero ρ₁ γ₁ →
          let b := FirstMode ρ₁
          let d₁ := FirstSlope ρ₁
          let r : ℝ → ℕ := fun x => FirstShellIndex ρ₁ x
          let H : ℝ → ℂ := fun x =>
            PoissonTuránSquare S_f (r x) x
          let normalized : ℝ → ℂ := fun x =>
            ((x : ℂ) ^ r x / (Nat.factorial (r x) : ℂ)) * H x
          let leading : ℝ → ℂ := fun x =>
            (b - starRingEnd ℂ b) ^ 2 /
              (Real.sqrt (2 * Real.pi * d₁ * x) : ℂ)
          let magnitudeConstant : ℝ :=
            4 * b.im ^ 2 /
              Real.sqrt (2 * Real.pi * d₁)
          (∃ error : ℝ → ℂ,
            Tendsto error atTop (𝓝 0) ∧
              ∀ᶠ x : ℝ in atTop,
                normalized x = leading x * (1 + error x)) ∧
          0 < magnitudeConstant ∧
          (fun x : ℝ => ‖normalized x‖) ~[atTop]
            (fun x : ℝ => magnitudeConstant * Real.rpow x (-1 / 2)) ∧
          (∀ᶠ x : ℝ in atTop,
            (normalized x).im = 0 ∧ (normalized x).re < 0)

end

end MathlibPlus.Open.ResearchFormalization.O0356.Claim15678
