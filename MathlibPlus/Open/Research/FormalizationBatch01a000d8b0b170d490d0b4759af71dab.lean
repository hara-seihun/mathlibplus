import Mathlib

noncomputable section

open MeasureTheory

namespace MathlibPlus.Open.Research

/-- The local algebraic content of the first-projective determinant claim. -/
def firstDerivativeDoubleZeroDiscriminant : Prop :=
  ∀ (S B : ℂ → ℂ) (z : ℂ),
    DifferentiableAt ℂ S z ∧ DifferentiableAt ℂ B z ∧ S z ≠ 0 →
      let F : ℂ → ℂ := fun w => S w + B w
      let r : ℂ → ℂ := fun w => -B w / S w
      let Δ : ℂ → ℂ := fun w => S w * deriv B w - B w * deriv S w
      (F z = 0 →
          B z = -S z ∧
          Δ z = S z * (deriv B z + deriv S z) ∧
          Δ z = S z * deriv F z ∧
          deriv F z = Δ z / S z) ∧
        ((F z = 0 ∧ deriv F z = 0) ↔ (r z = 1 ∧ Δ z = 0))

/-- The single-face logarithmic derivative identity, pointwise on its face. -/
def singleFaceLogarithmicDerivativeFormula : Prop :=
  ∀ (L : ℝ) (Φ₀ Φ₁ a₀ a₁ ε : ℂ → ℂ) (z : ℂ),
    DifferentiableAt ℂ Φ₀ z ∧
      DifferentiableAt ℂ Φ₁ z ∧
      DifferentiableAt ℂ a₀ z ∧
      DifferentiableAt ℂ a₁ z ∧
      DifferentiableAt ℂ ε z ∧
      a₀ z ≠ 0 ∧ a₁ z ≠ 0 ∧ 1 + ε z ≠ 0 →
      let S : ℂ → ℂ := fun w => Complex.exp (-((L : ℂ) * Φ₀ w)) * a₀ w
      let B : ℂ → ℂ :=
        fun w => Complex.exp (-((L : ℂ) * Φ₁ w)) * a₁ w * (1 + ε w)
      let Δ : ℂ → ℂ := fun w => S w * deriv B w - B w * deriv S w
      Δ z / (S z * B z) =
        -(L : ℂ) * (deriv Φ₁ z - deriv Φ₀ z) +
          deriv a₁ z / a₁ z - deriv a₀ z / a₀ z +
            deriv ε z / (1 + ε z)

/-- Fourier transform with the convention used by the admitted Poisson statements. -/
def researchFourier (q : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, (q x : ℂ) * Complex.exp (-(2 * Real.pi) * Complex.I * (x * ξ : ℂ))

/-- The exact Poisson-gauge identity, including its support consequence. -/
def exactPoissonGaugeIdentity : Prop :=
  ∀ (L : ℝ) (q : ℝ → ℝ),
    Integrable q ∧
      (∀ x : ℝ, q (-x) = q x) ∧
      (∫ x : ℝ, q x = 0) ∧
      (∀ x : ℝ, |x| > Real.exp L → q x = 0) ∧
      q (Real.exp L) = 0 ∧ q (-(Real.exp L)) = 0 →
      let Kq : ℝ → ℂ := fun x =>
        (Real.exp (x / 2) : ℂ) *
          ∑' n : ℕ, (q (((n + 1 : ℕ) : ℝ) * Real.exp x) : ℂ)
      (∀ x : ℝ,
          Kq x =
            -(q 0 : ℂ) / 2 * (Real.exp (x / 2) : ℂ) +
              (Real.exp (-x / 2) : ℂ) *
                ∑' k : ℕ, researchFourier q (((k + 1 : ℕ) : ℝ) * Real.exp (-x))) ∧
        (∀ x : ℝ, x ≥ L → Kq x = 0)

/-- The zero-mean annular Mellin density assertion, with the standard
continuous-on/holomorphic-on-interior meaning of `A(K)`. -/
def annularMellin (p : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x in Set.Ioo (1 : ℝ) 2,
    p x * Complex.exp ((s - 1) * (Real.log x : ℂ))

def isAnnularA (K : Set ℂ) (G : ℂ → ℂ) : Prop :=
  ContinuousOn G K ∧ DifferentiableOn ℂ G (interior K)

def zeroMeanAnnularMellinDensity : Prop :=
  ∀ (K : Set ℂ),
    IsCompact K → IsConnected Kᶜ →
      (((1 : ℂ) ∈ K →
          ∀ (G : ℂ → ℂ),
            isAnnularA K G → G 1 = 0 →
              ∀ ε : ℝ, 0 < ε →
                ∃ p : ℝ → ℂ,
                  ContDiff ℝ ⊤ p ∧
                    (∀ x : ℝ,
                      x ∉ Set.Ioo (1 : ℝ) 2 → p x = 0) ∧
                    (∫ x in Set.Ioo (1 : ℝ) 2, p x) = 0 ∧
                    ∀ s ∈ K, ‖annularMellin p s - G s‖ < ε) ∧
        ((1 : ℂ) ∉ K →
          ∀ (G : ℂ → ℂ),
            isAnnularA K G →
              ∀ ε : ℝ, 0 < ε →
                ∃ p : ℝ → ℂ,
                  ContDiff ℝ ⊤ p ∧
                    (∀ x : ℝ,
                      x ∉ Set.Ioo (1 : ℝ) 2 → p x = 0) ∧
                    (∫ x in Set.Ioo (1 : ℝ) 2, p x) = 0 ∧
                    ∀ s ∈ K, ‖annularMellin p s - G s‖ < ε))

end MathlibPlus.Open.Research
