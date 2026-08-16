import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.O0252

open scoped Topology
open Set
open Filter

/-- Claim 15014: on the exact transition rectangles of Claim 15011, the
upper wave has the displayed quotient and a uniform exponential bound.  The
amplitude is the nonzero negative leading-Dini coefficient fixed by Claim
15010, rather than an unconstrained family. -/
noncomputable def claim15014_upperWaveUniformlyNegligible : Prop :=
  ∀ (k : ℕ) (α : ℝ) (a : ℝ → ℝ) (y₀ y₁ δ : ℝ),
    1 ≤ k →
    0 < α →
    0 < y₀ →
    y₀ < y₁ →
    y₁ < 1 / 2 →
    0 < δ →
    δ < (1 / 2 : ℝ) * min y₀ ((1 / 2 : ℝ) - y₁) →
    (∀ L : ℝ, 0 < L → 0 < a L) →
    Tendsto (fun L : ℝ => Real.log (a L) / L) atTop (𝓝 0) →
    let exponent : ℝ := (1 : ℝ) / (2 * (k : ℝ))
    let κ : ℝ → ℝ := fun y =>
      Real.rpow (((5 / 2 : ℝ) - y) / α) exponent
    let T : ℝ → ℝ := fun L => Real.rpow L exponent
    let R : ℝ → Set ℂ := fun L =>
      {z : ℂ | ∃ x y : ℝ,
        x ∈ Set.Icc (κ y₁ * T L) (κ y₀ * T L) ∧
          y ∈ Set.Icc (y₀ - 2 * δ) (y₁ + 2 * δ) ∧
          z = (x : ℂ) + Complex.I * (y : ℂ)}
    let G : ℝ → ℂ → ℂ := fun L z =>
      (z * Complex.sin ((L : ℂ) * z) -
          (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
        (z ^ 2 + (1 / 4 : ℂ))
    let A : ℝ → ℝ := fun L =>
      -a L * Real.exp (-5 * L / 2)
    let Dminus : ℝ → ℂ → ℂ := fun L z =>
      (A L : ℂ) * (Complex.I / 2) *
          Complex.exp (-Complex.I * (L : ℂ) * z) /
        (z - Complex.I / 2)
    let error : ℝ → ℂ → ℂ := fun L z =>
      ((A L : ℂ) * G L z - Dminus L z) /
        Dminus L z
    ∃ C L₀ : ℝ,
      0 ≤ C ∧
        0 < L₀ ∧
          ∀ L : ℝ, L₀ ≤ L →
            ∀ z : ℂ, z ∈ R L →
              error L z =
                  -Complex.exp (2 * Complex.I * (L : ℂ) * z) *
                    (z - Complex.I / 2) / (z + Complex.I / 2) ∧
                ‖error L z‖ ≤
                  C * Real.exp (-2 * L * (y₀ - 2 * δ))

end MathlibPlus.Open.ResearchFormalization.O0252
