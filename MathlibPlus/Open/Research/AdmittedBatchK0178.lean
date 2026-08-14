import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.K0178

/-- A closed real rectangle embedded in the complex plane. -/
def rectangle9856 (x₀ x₁ y₀ y₁ : ℝ) : Set ℂ :=
  {z | ∃ x y : ℝ,
    x₀ ≤ x ∧ x ≤ x₁ ∧ y₀ ≤ y ∧ y ≤ y₁ ∧
      z = (x : ℂ) + (y : ℂ) * Complex.I}

def sigma9856 (S B : ℂ → ℂ) (z : ℂ) : ℂ := -B z / S z

def a9856 (L : ℝ) (S B : ℂ → ℂ) (x y : ℝ) : ℝ :=
  L⁻¹ * Real.log ‖sigma9856 S B ((x : ℂ) + (y : ℂ) * Complex.I)‖

def dx9856 (L : ℝ) (S B : ℂ → ℂ) (x y : ℝ) : ℝ :=
  deriv (fun x' : ℝ => a9856 L S B x' y) x

def dy9856 (L : ℝ) (S B : ℂ → ℂ) (x y : ℝ) : ℝ :=
  deriv (fun y' : ℝ => a9856 L S B x y') y

/-- Claim 9856: a uniformly transverse vertical crossing is one smooth graph. -/
def claim9856 : Prop :=
  ∀ (x₀ x₁ y₀ y₁ L τ₀ : ℝ) (S B : ℂ → ℂ),
    x₀ ≤ x₁ → y₀ < y₁ → 0 < τ₀ →
    (∃ U : Set ℂ,
      IsOpen U ∧ rectangle9856 x₀ x₁ y₀ y₁ ⊆ U ∧
      DifferentiableOn ℂ S U ∧ DifferentiableOn ℂ B U ∧
      (∀ z ∈ U, S z ≠ 0 ∧ B z ≠ 0)) →
    (∀ x : ℝ, x₀ ≤ x → x ≤ x₁ →
      a9856 L S B x y₀ < 0 ∧ 0 < a9856 L S B x y₁) →
    (∀ x y : ℝ, x₀ ≤ x → x ≤ x₁ → y₀ ≤ y → y ≤ y₁ →
      τ₀ ≤ dy9856 L S B x y) →
    ∃ g : ℝ → ℝ,
      (∀ x : ℝ, x₀ ≤ x → x ≤ x₁ →
        y₀ < g x ∧ g x < y₁ ∧ a9856 L S B x (g x) = 0 ∧
        (∀ y : ℝ, y₀ < y → y < y₁ →
          a9856 L S B x y = 0 → y = g x)) ∧
      ContDiffOn ℝ ⊤ g (Set.Icc x₀ x₁) ∧
      (∀ x : ℝ, x₀ ≤ x → x ≤ x₁ →
        deriv g x =
          -(dx9856 L S B x (g x)) /
            dy9856 L S B x (g x))

end MathlibPlus.Open.Research.K0178
