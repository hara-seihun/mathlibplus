import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The scalar potential appearing after gauging the Hedenmalm pencil. -/
def gaugedHedenmalmQ (a : ℝ → ℝ) (spectralParameter x : ℝ) : ℝ :=
  (a x ^ 2 + 2 * deriv a x - 2 * a x * spectralParameter +
    spectralParameter ^ 2) / 4

/-- The pointwise action of the gauged Hedenmalm pencil on a scalar function. -/
def gaugedHedenmalmPencil
    (a : ℝ → ℝ) (spectralParameter : ℝ) (y : ℝ → ℂ) (x : ℝ) : ℂ :=
  (spectralParameter : ℂ) ^ 2 * y x -
    2 * (a x : ℂ) * (spectralParameter : ℂ) * y x +
    4 * (-(deriv (deriv y) x) +
      (1 / 2 : ℂ) * ((deriv (𝕜 := ℝ) a) x : ℂ) * y x +
      (1 / 4 : ℂ) * (a x : ℂ) ^ 2 * y x)

/--
For a real even source `h = exp (-φ)` and `a = φ'`, the zero-mode
of the gauged pencil is exactly the displayed scalar equation.
-/
def gaugedHedenmalmZeroModeEquation : Prop :=
  ∀ (h φ : ℝ → ℝ) (a : ℝ → ℝ) (spectralParameter : ℝ) (y : ℝ → ℂ),
    (Function.Even h ∧
      (∀ x, h x = Real.exp (-(φ x))) ∧
      (∀ x, a x = deriv φ x)) →
      ((∀ x, gaugedHedenmalmPencil a spectralParameter y x = 0) ↔
        (∀ x, deriv (deriv y) x =
          (gaugedHedenmalmQ a spectralParameter x : ℂ) * y x))

end

end MathlibPlus.Open.Analysis
