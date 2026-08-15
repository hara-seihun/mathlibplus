import Mathlib

namespace MathlibPlus.Open.Analysis

abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev UnitPhase := {z : ℂ // ‖z‖ = 1}

noncomputable def higherPrimePowerRemainder
    (ω : PrimeIndex → UnitPhase) (s : ℂ) : ℂ :=
  ∑' p : PrimeIndex, ∑' r : ℕ,
    (ω p : ℂ) ^ (r + 2) /
      (((r + 2 : ℕ) : ℂ) *
        Complex.exp (((r + 2 : ℕ) : ℂ) * s * (Real.log (p.1 : ℝ) : ℂ)))

noncomputable def higherPrimePowerWeightTerm (σ : ℝ) (p : PrimeIndex) : ℝ :=
  Real.log (p.1 : ℝ) * Real.rpow (p.1 : ℝ) (-2 * σ) /
    (1 - Real.rpow (p.1 : ℝ) (-σ))

noncomputable def higherPrimePowerWeight (σ : ℝ) : ℝ :=
  ∑' p : PrimeIndex, higherPrimePowerWeightTerm σ p

def shortArcInHalfPlane (σ ℓ : ℝ) (a b : ℂ) : Prop :=
  0 ≤ ℓ ∧ ∃ γ : ℝ → ℂ,
    ContinuousOn γ (Set.Icc 0 1) ∧
      γ 0 = a ∧ γ 1 = b ∧
      (∀ t ∈ Set.Icc 0 1, σ ≤ (γ t).re) ∧
      eVariationOn γ (Set.Icc 0 1) = ENNReal.ofReal ℓ

/-- The higher-prime-power endpoint term has a uniform linear bound along the short arc. -/
def higherPrimePowerEndpointTermOnlyLinear : Prop :=
  ∀ (σ ℓ : ℝ) (a b : ℂ),
    1 / 2 < σ →
    shortArcInHalfPlane σ ℓ a b →
    Summable (fun p : PrimeIndex => higherPrimePowerWeightTerm σ p) ∧
      ∀ ω : PrimeIndex → UnitPhase,
        ‖higherPrimePowerRemainder ω b - higherPrimePowerRemainder ω a‖ ≤
          higherPrimePowerWeight σ * ℓ

end MathlibPlus.Open.Analysis
