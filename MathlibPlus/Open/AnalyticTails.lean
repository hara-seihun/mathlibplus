import Mathlib

open scoped Classical BigOperators
noncomputable section

namespace MathlibPlus.Open.AnalyticTails

/-- Claim 4049. -/
def claim4049_exactDerivativeLadderAtFixedCutoff : Prop :=
  ∀ (K : ℕ → ℝ → ℝ → ℝ) (T : ℝ) (r : ℕ),
    (∀ x t, deriv (fun y => K r y t) x = K (r + 1) x t) ∧
      ∀ x, deriv (fun y => ∫ t in Set.Icc (0 : ℝ) T, K r y t) x =
        ∫ t in Set.Icc (0 : ℝ) T, K (r + 1) x t

/-- Claim 4050. -/
def claim4050_weightedPrimeCountingDiscrepancy : Prop :=
  ∃ C₀ c₀ T₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
    ∀ t : ℝ, T₀ ≤ t → ∃ ε : ℝ,
      (∃ D : ℝ, D = -0 + ε) ∧
        |ε| ≤ C₀ * Real.exp (-c₀ * t ^ (3 / 5 : ℝ) /
          (Real.log t) ^ (1 / 5 : ℝ))

/-- Claim 4051. -/
def claim4051_exactStieltjesTailIdentity : Prop :=
  ∀ (R K : ℝ → ℝ → ℝ) (ε : ℝ → ℝ) (x T : ℝ),
    R x T = -(K x T) * (ε T) + ∫ t : ℝ, (ε t) * (K x t)

/-- Claim 4053. -/
def claim4053_uniformDyadicTailExponent : Prop :=
  ∃ c₁ A : ℝ, 0 < c₁ ∧ 0 < A ∧
    ∀ (r : ℕ) (x T : ℝ), (r : ℝ) ≤ A * x →
      ∃ C : ℝ, Real.log |(r : ℝ) + 1| ≤
        (A * x / 2) * Real.log (T / x) -
          c₁ * T ^ (3 / 5 : ℝ) / (Real.log T) ^ (1 / 5 : ℝ) + C * Real.log T

end MathlibPlus.Open.AnalyticTails
