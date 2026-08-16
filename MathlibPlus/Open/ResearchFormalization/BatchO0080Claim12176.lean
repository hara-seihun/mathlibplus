import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchO0080

/-- The exact square-port derivative identities. -/
def claim12176 : Prop :=
  ∀ (σ t r : ℝ), -4 < σ → 0 < r →
    let c : ℝ := (32 : ℝ) / 10395
    let g₆ : ℝ → ℝ := fun u =>
      (1 / 12 : ℝ) *
        (∑ n ∈ Finset.Icc 1 (Nat.floor (Real.exp u)),
          (((n : ℝ) / Real.exp u) ^ 2) *
            (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4)
    let β₆ : ℝ → ℝ := fun u => g₆ u - c * Real.exp u
    let h₆ : ℝ → ℝ := fun u => deriv β₆ u - β₆ u
    let B : ℂ → ℂ := fun s =>
      ∫ u : ℝ in Set.Ioi 0, (β₆ u : ℂ) * Complex.exp (-s * (u : ℂ))
    let H₆ : ℂ → ℂ := fun s => c + (s - 1) * B s
    let I : (ℝ → ℝ) → ℂ := fun P =>
      ∫ u : ℝ in Set.Ioi 0,
        (P u : ℂ) * (h₆ u : ℂ) *
          Complex.exp (-(σ : ℂ) * (u : ℂ) + Complex.I * (t : ℂ) * (u : ℂ))
    let z : ℂ := (σ : ℂ) - Complex.I * (t : ℂ)
    let S₀ : ℂ := I (fun u => u ^ 2)
    let S₁ : ℂ := I (fun u => u * (2 * r - u))
    let S₂ : ℂ := I (fun u => (u - 2 * r) ^ 2)
    S₀ = deriv (deriv H₆) z ∧
      S₁ = -deriv (deriv H₆) z - (2 * r : ℂ) * deriv H₆ z ∧
      S₂ = deriv (deriv H₆) z + (4 * r : ℂ) * deriv H₆ z +
        (4 * r ^ 2 : ℂ) * H₆ z

end MathlibPlus.Open.ResearchFormalization.BatchO0080
