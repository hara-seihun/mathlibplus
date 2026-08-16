import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.SeriesHardEdgeClaims

def powerSeriesValue (a : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (a n : ℂ) * z ^ n

def entirePowerSeries (a : ℕ → ℝ) : Prop :=
  ∀ z : ℂ, Summable (fun n : ℕ => (a n : ℂ) * z ^ n)

def tailCoefficient (a : ℕ → ℝ) (alpha : ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, a (n + 1 + j) * alpha ^ j

def endpointExteriorCoefficient (a : ℕ → ℝ) (alpha b : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then
    tailCoefficient a alpha n.toNat
  else
    b * alpha ^ (Int.toNat (-n) - 1)

def twoByTwoDet (x00 x01 x10 x11 : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 2 =>
    if i.1 = 0 then
      if j.1 = 0 then x00 else x01
    else
      if j.1 = 0 then x10 else x11)

def hardEdgeDeltaZero (d : ℤ → ℝ) : ℝ :=
  twoByTwoDet (d 0) (d 1) (d (-1)) (d 0)

def hardEdgeDeltaOne (d : ℤ → ℝ) : ℝ :=
  twoByTwoDet (d 1) (d 2) (d (-1)) (d 0)

def hardEdgeDeltaTwo (d : ℤ → ℝ) : ℝ :=
  twoByTwoDet (d 1) (d 2) (d 0) (d 1)

def rankTwoShiftOneBlock (d : ℤ → ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  fun i j => d (1 + (j.1 : ℤ) - (i.1 : ℤ))

/-- The hard-edge shift-one implication, with the endpoint and positivity
hypotheses retained in the implication. -/
def claim12084 : Prop :=
  ∀ (a : ℕ → ℝ) (alpha b : ℝ),
    entirePowerSeries a →
    powerSeriesValue a (alpha : ℂ) = (b : ℂ) →
    0 < alpha →
    (∀ n : ℕ, 0 < a n) →
    tailCoefficient a alpha 0 > a 1 →
    a 1 ^ 2 > 2 * a 0 * a 2 →
    2 * a 0 > b →
    let d : ℤ → ℝ := endpointExteriorCoefficient a alpha b
    hardEdgeDeltaZero d - alpha * hardEdgeDeltaOne d > 0

def ftPolynomial (t : ℝ) : Polynomial ℝ :=
  Polynomial.C (1 : ℝ) +
    Polynomial.C (t / 2) * Polynomial.X +
    Polynomial.C (t ^ 2 / 4) * Polynomial.X ^ 2

def ftSequence (t : ℝ) : ℕ → ℝ :=
  fun n => (ftPolynomial t).coeff n

/-- The exact rank-two, shift-one block and its three deleted-row cofactors
for the scale-free quadratic family. -/
def claim12087 : Prop :=
  ∀ t : ℝ, 0 < t →
    let F : Polynomial ℝ := ftPolynomial t
    let a : ℕ → ℝ := ftSequence t
    let alpha : ℝ := 1 / 4
    let b : ℝ := Polynomial.eval alpha F
    let d : ℤ → ℝ := endpointExteriorCoefficient a alpha b
    let B : Matrix (Fin 3) (Fin 2) ℝ := rankTwoShiftOneBlock d
    B (0 : Fin 3) (0 : Fin 2) = t ^ 2 / 4 ∧
    B (0 : Fin 3) (1 : Fin 2) = 0 ∧
    B (1 : Fin 3) (0 : Fin 2) = t * (t + 8) / 16 ∧
    B (1 : Fin 3) (1 : Fin 2) = t ^ 2 / 4 ∧
    B (2 : Fin 3) (0 : Fin 2) = (t ^ 2 + 8 * t + 64) / 64 ∧
    B (2 : Fin 3) (1 : Fin 2) = t * (t + 8) / 16 ∧
    hardEdgeDeltaZero d = t ^ 3 / 32 ∧
    hardEdgeDeltaOne d = t ^ 3 * (t + 8) / 64 ∧
    hardEdgeDeltaTwo d = t ^ 4 / 16

end MathlibPlus.Open.ResearchFormalization.SeriesHardEdgeClaims
