import Mathlib

open scoped Topology
open Asymptotics Filter

namespace MathlibPlus.Open.ResearchFormalization

/-- A fixed absolute-width packet around a frequency carrier. -/
def frequencyPacket (ω W : ℝ) : Set ℝ :=
  Set.Icc (ω - W) (ω + W)

/-- The carrier coordinate for ξ = λ exp y. -/
noncomputable def logarithmicCarrier (lambda ω : ℝ) : ℝ :=
  Real.log (ω / lambda)

/-- The image in logarithmic coordinates of a fixed-width frequency packet. -/
noncomputable def logarithmicPacket (lambda W ω : ℝ) : Set ℝ :=
  Set.Icc (Real.log ((ω - W) / lambda)) (Real.log ((ω + W) / lambda))

/-- The width of that packet in logarithmic coordinates. -/
noncomputable def logarithmicPacketWidth (lambda W ω : ℝ) : ℝ :=
  Real.log ((ω + W) / lambda) - Real.log ((ω - W) / lambda)

/--
Claim 14982: under ξ = λ exp y, a fixed absolute-width packet around a
carrier tending to infinity has carrier center log (ω / λ), logarithmic
width O (1 / ω), and hence vanishing relative and logarithmic widths.
-/
def claim14982 : Prop :=
  ∀ (lambda W : ℝ) (ω : ℝ → ℝ),
    0 < lambda →
    0 < W →
    Filter.Tendsto ω Filter.atTop Filter.atTop →
    let ξ : ℝ → ℝ := fun y => lambda * Real.exp y
    let y₀ : ℝ → ℝ := fun r => logarithmicCarrier lambda (ω r)
    let logPacket : ℝ → Set ℝ := fun r => logarithmicPacket lambda W (ω r)
    let relativeWidth : ℝ → ℝ := fun r => (2 * W) / ω r
    let logWidth : ℝ → ℝ := fun r => logarithmicPacketWidth lambda W (ω r)
    (∀ᶠ r in Filter.atTop,
      W < ω r ∧
        frequencyPacket (ω r) W ⊆ Set.Ioi 0 ∧
        ξ (y₀ r) = ω r ∧
        y₀ r ∈ logPacket r) ∧
      (∀ r : ℝ, (ω r + W) - (ω r - W) = 2 * W) ∧
      Asymptotics.IsBigO Filter.atTop logWidth (fun r => 1 / ω r) ∧
      Filter.Tendsto relativeWidth Filter.atTop (𝓝 0) ∧
      Filter.Tendsto logWidth Filter.atTop (𝓝 0)

end MathlibPlus.Open.ResearchFormalization
