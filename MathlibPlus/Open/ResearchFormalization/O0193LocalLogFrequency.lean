import Mathlib

open Asymptotics Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0193LocalLogFrequency

noncomputable section

/-- A symmetric pair of identical smooth compactly supported bumps centered at
`±x₀`, with the pair contained in the open source band. -/
def symmetricPairBump (lambda x₀ : ℝ) (b : ℝ → ℝ) : Prop :=
  0 < lambda ∧
    0 < x₀ ∧
      x₀ < lambda ∧
        (∃ r : ℝ,
          0 < r ∧
            x₀ + r < lambda ∧
              (∃ z : ℝ, b z ≠ 0) ∧
                Function.Even b ∧
                  ContDiff ℝ (⊤ : WithTop ℕ∞) b ∧
                    HasCompactSupport b ∧
                      Function.support b ⊆ Set.Ioo (-r) r) ∧
          Function.support (fun x => b (x - x₀) + b (x + x₀)) ⊆
            Set.Ioo (-lambda) lambda

/-- The symmetric pair `η(x)=b(x-x₀)+b(x+x₀)`. -/
def symmetricPair (b : ℝ → ℝ) (x₀ : ℝ) : ℝ → ℝ :=
  fun x => b (x - x₀) + b (x + x₀)

/-- The source modulation attached to the symmetric pair. -/
def cosinePairPacket (b : ℝ → ℝ) (x₀ ω : ℝ) : ℝ → ℝ :=
  fun x => symmetricPair b x₀ x * Real.cos (ω * x)

/-- The fixed unitary real-line Fourier convention used for these packets. -/
noncomputable def unitaryFourier (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
    ∫ x : ℝ,
      (f x : ℂ) * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))

/-- The translated positive Fourier packet of the cosine modulation. -/
noncomputable def positiveFourierPacket
    (b : ℝ → ℝ) (x₀ ω ξ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * unitaryFourier (symmetricPair b x₀) (ξ - ω)

/-- The translated negative Fourier packet of the cosine modulation. -/
noncomputable def negativeFourierPacket
    (b : ℝ → ℝ) (x₀ ω ξ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * unitaryFourier (symmetricPair b x₀) (ξ + ω)

/-- The logarithmic carrier center `y₀=log(ω/λ)`. -/
noncomputable def logCarrierCenter (lambda ω : ℝ) : ℝ :=
  Real.log (ω / lambda)

/-- The phase of the positive pair factor after `ξ=λ exp y`. -/
noncomputable def logarithmicPairPhase
    (lambda x₀ ω y : ℝ) : ℝ :=
  x₀ * (lambda * Real.exp y - ω)

/-- The local logarithmic frequency, defined as the phase derivative at the
packet center. -/
noncomputable def localLogFrequency
    (lambda x₀ ω : ℝ) : ℝ :=
  deriv (fun y : ℝ => logarithmicPairPhase lambda x₀ ω y)
    (logCarrierCenter lambda ω)

/-- The logarithmic cosine expansion on the fixed-width scale. -/
def logarithmicCosineExpansion
    (lambda x₀ : ℝ) : Prop :=
  ∀ h : ℝ,
    ∃ r : ℝ → ℝ,
      Asymptotics.IsLittleO Filter.atTop r
          (fun _ : ℝ => (1 : ℝ)) ∧
        ∀ ω : ℝ,
          logarithmicPairPhase lambda x₀ ω
              (logCarrierCenter lambda ω + h / ω) =
            x₀ * ω * h / ω + r ω

/-- Claim 14983: the symmetric pair has the exact positive packet cosine
factor, and on the fixed-width logarithmic scale its phase is
`x₀ω(y-y₀)+o(1)`, with local frequency `x₀ω+o(ω)`. -/
def claim14983 : Prop :=
  ∀ (lambda x₀ : ℝ) (b : ℝ → ℝ),
    symmetricPairBump lambda x₀ b →
      (∀ ω ξ : ℝ,
        unitaryFourier (cosinePairPacket b x₀ ω) ξ =
          positiveFourierPacket b x₀ ω ξ +
            negativeFourierPacket b x₀ ω ξ) ∧
      (∀ ω ξ : ℝ,
        positiveFourierPacket b x₀ ω ξ =
          (Real.cos (x₀ * (ξ - ω)) : ℂ) *
            unitaryFourier b (ξ - ω)) ∧
      logarithmicCosineExpansion lambda x₀ ∧
      Asymptotics.IsLittleO Filter.atTop
        (fun ω : ℝ =>
          localLogFrequency lambda x₀ ω - x₀ * ω)
        (fun ω : ℝ => ω)

end

end MathlibPlus.Open.ResearchFormalization.O0193LocalLogFrequency
