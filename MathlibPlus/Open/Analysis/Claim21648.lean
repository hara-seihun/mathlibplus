import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- Claim 21648: the exact two-wave phase is univalent, positively oriented,
with the stated real-axis seam and wave-relative attenuation. -/
def claim21648 : Prop :=
  let τ : ℝ := 63 / 1000
  let T : ℝ := 1629 / 10000
  let X₀ : ℝ := 51 * 10 ^ 74
  let sPlus : ℂ → ℂ := fun z => (1 + Complex.I * z) / 2
  let sMinus : ℂ → ℂ := fun z => (1 - Complex.I * z) / 2
  let M₀ : ℂ → ℂ := fun s =>
    (1 / 8 : ℂ) * (s * (s - 1) / 2) *
      Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) *
      (Real.sqrt (2 * Real.pi) : ℂ) *
      Complex.exp ((s / 2 - 1 / 2) * Complex.log (s / 2) - s / 2)
  let α : ℂ → ℂ := fun s =>
    1 / (2 * s) + 1 / (s - 1) +
      (1 / 2 : ℂ) * Complex.log (s / (2 * (Real.pi : ℂ)))
  let M : ℝ → ℂ → ℂ := fun t s =>
    Complex.exp ((t : ℂ) * (α s) ^ 2 / 4) * M₀ s
  let γ : ℝ → ℂ → ℂ := fun t z =>
    M t (sPlus z) / M t (sMinus z)
  let g : ℝ → ℂ → ℂ := fun t z =>
    -Complex.I * Complex.log (γ t z)
  let u : ℝ → ℂ → ℝ := fun t z => (g t z).re
  let v : ℝ → ℂ → ℝ := fun t z => (g t z).im
  let m : ℝ → ℝ := fun x =>
    Real.log (x / (4 * Real.pi)) / 2 - 4 / x ^ 2 -
      T * (Real.log (x / (4 * Real.pi)) / 2 + 2) / x
  let D : Set ℂ := {z | z.re > X₀ ∧ |z.im| < 1}
  (∀ t, τ ≤ t → t ≤ T →
    (∀ ⦃z w : ℂ⦄, z ∈ D → w ∈ D → g t z = g t w → z = w) ∧
    (∀ z, z ∈ D → (deriv (g t) z).re > 0) ∧
    (∀ z, z ∈ D →
      deriv (fun x : ℝ => u t ((x : ℂ) + Complex.I * (z.im : ℂ))) z.re =
          (deriv (g t) z).re ∧
        deriv (fun y : ℝ => v t ((z.re : ℂ) + Complex.I * (y : ℂ))) z.im =
          (deriv (g t) z).re) ∧
    (∀ x, X₀ ≤ x → v t (x : ℂ) = 0) ∧
    (∀ z, z ∈ D →
      (0 < z.im ↔ 0 < v t z) ∧ (z.im < 0 ↔ v t z < 0)) ∧
    (∀ z, z ∈ D → 0 ≤ z.im →
      let r := ‖γ t z‖
      0 < r ∧ r = Real.exp (-v t z) ∧ r ≤ 1 ∧
        r ≤ Real.exp (-m z.re * z.im)))

end MathlibPlus.Open.Analysis
