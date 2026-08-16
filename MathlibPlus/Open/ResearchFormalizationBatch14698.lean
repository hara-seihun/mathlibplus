import Mathlib

noncomputable section

open Asymptotics Filter

namespace MathlibPlus.Open.ResearchFormalizationBatch14698

/-- The exact two-Gaussian transform fixed by the admitted zero claims. -/
def FMinus (z : ℂ) : ℂ :=
  Complex.exp (-(z ^ 2)) + Complex.exp (-(2 * z ^ 2))

/-- The natural-indexed radius in the admitted zero sequence. -/
def rIndex (k : ℕ) : ℝ :=
  Real.sqrt (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2)

/-- The exact complex points from the admitted two-Gaussian zero statement. -/
def wIndex (k : ℕ) : ℂ :=
  -(rIndex k : ℂ) + Complex.I * (rIndex k : ℂ)

/-- Multiplication of the source by `2 cosh (a t)` produces these two
imaginary shifts of the transform. -/
def imaginaryShift (a : ℝ) : ℂ :=
  Complex.I * (a : ℂ)

def shiftedTransform (a : ℝ) (z : ℂ) : ℂ :=
  FMinus (z + imaginaryShift a) + FMinus (z - imaginaryShift a)

/-- The center `z_k = w_k - i a` of the Rouché circle. -/
def zIndex (a : ℝ) (k : ℕ) : ℂ :=
  wIndex k - imaginaryShift a

/-- The radius of the Rouché circle in the admitted statement. -/
def roucheRadius (a : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-3 * a * rIndex k) / rIndex k

/-- The explicit error scale used by the fixed-`a` asymptotics. -/
def shiftedResidual (a : ℝ) (k : ℕ) : ℂ :=
  FMinus (wIndex k - 2 * imaginaryShift a)

def shiftedResidualScale (a : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-4 * a * rIndex k)

/-- Claim 14698: at `z_k = w_k - i a`, the first shifted summand vanishes,
the displayed real-part identity holds, and the other summand has the stated
fixed-`a` exponential bound. -/
def claim14698 : Prop :=
  ∀ a : ℝ, 0 < a →
    (∀ k : ℕ,
      FMinus (zIndex a k + imaginaryShift a) = 0 ∧
      ((wIndex k - 2 * imaginaryShift a) ^ 2).re =
        4 * a * rIndex k - 4 * a ^ 2) ∧
    IsBigO atTop
      (fun k : ℕ => ‖shiftedResidual a k‖)
      (fun k : ℕ => shiftedResidualScale a k)

/-- Claim 14699: for each fixed positive shift, the displayed term dominates
on the displayed circle eventually, and the resulting zeros have the stated
fixed-`a` displacement. -/
def claim14699 : Prop :=
  ∀ a : ℝ, 0 < a →
    ∃ ζ : ℕ → ℂ,
      (∀ᶠ k : ℕ in atTop,
        ∀ z : ℂ,
          ‖z - zIndex a k‖ = roucheRadius a k →
            ‖FMinus (z + imaginaryShift a)‖ >
              ‖FMinus (z - imaginaryShift a)‖) ∧
      (∀ᶠ k : ℕ in atTop, shiftedTransform a (ζ k) = 0) ∧
      IsBigO atTop
        (fun k : ℕ => ‖ζ k - zIndex a k‖)
        (fun k : ℕ => Real.exp (-4 * a * rIndex k) / rIndex k)

end MathlibPlus.Open.ResearchFormalizationBatch14698
