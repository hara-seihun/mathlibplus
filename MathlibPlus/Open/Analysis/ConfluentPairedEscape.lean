import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The positive paired kernel from the admitted rate-pair statement. -/
def pairedP (a b u v : ℝ) : ℝ :=
  Real.cosh (a * u) * Real.cosh (b * v) +
    Real.cosh (a * v) * Real.cosh (b * u)

/-- The rate generator `b ∂ₐ - a ∂ᵦ` applied to the paired kernel. -/
def pairedRateGenerator (a b u v : ℝ) : ℝ :=
  b * deriv (fun a' : ℝ => pairedP a' b u v) a -
    a * deriv (fun b' : ℝ => pairedP a b' u v) b

/-- The removable value of the paired density on the confluent face `a = b`. -/
def pairedConfluentKhat (a u v : ℝ) : ℝ :=
  (u * v * Real.sinh (a * u) * Real.sinh (a * v)) / 2 -
    ((u ^ 2 + v ^ 2) * Real.cosh (a * u) * Real.cosh (a * v)) / 4 +
    (v * Real.cosh (a * u) * Real.sinh (a * v) +
      u * Real.cosh (a * v) * Real.sinh (a * u)) / (4 * a)

/-- The paired density, using its removable confluent value when the rates agree. -/
def pairedKhat (a b u v : ℝ) : ℝ :=
  if a = b then pairedConfluentKhat a u v
  else pairedRateGenerator a b u v / (2 * (b ^ 2 - a ^ 2))

/-- The one-variable hyperbolic secant used by the two confluent ratios. -/
def pairedSech (t : ℝ) : ℝ := 1 / Real.cosh t

/-- The second partial derivative in the first spatial variable. -/
def pairedSecondU (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun x : ℝ => deriv (fun x' : ℝ => F x' v) x) u

/-- The second partial derivative in the second spatial variable. -/
def pairedSecondV (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  deriv (fun y : ℝ => deriv (fun y' : ℝ => F u y') y) v

/-- `L = ∂² - 1/4` in the first spatial variable. -/
def pairedLu (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  pairedSecondU F u v - (1 / 4 : ℝ) * F u v

/-- `L = ∂² - 1/4` in the second spatial variable. -/
def pairedLv (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  pairedSecondV F u v - (1 / 4 : ℝ) * F u v

/-- The Green operator `A = Lᵤ Lᵥ`. -/
def pairedA (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  pairedLu (fun x y => pairedLv F x y) u v

/-- The pair-dependent shift polynomial `fₐ,ᵦ(z) = z - Δₐ,ᵦ`. -/
def pairedDelta (a b : ℝ) : ℝ :=
  (a ^ 2 - (1 / 4 : ℝ)) * (b ^ 2 - (1 / 4 : ℝ))

def pairedEscapePolynomial (a b z : ℝ) : ℝ :=
  z - pairedDelta a b

/-- Opposite confluent age-face ratios, with `t = a * u`, and their two limits. -/
def oppositeConfluentAgeFaceRatios : Prop :=
  ∀ a : ℝ, (1 / 2 : ℝ) < a →
    (∀ u : ℝ,
      pairedKhat a a u 0 / pairedP a a u 0 =
        u * (Real.tanh (a * u) - a * u) / (8 * a)) ∧
    Filter.Tendsto
      (fun u : ℝ => pairedKhat a a u 0 / pairedP a a u 0)
      Filter.atTop Filter.atBot ∧
    (∀ u : ℝ,
      pairedKhat a a u u / pairedP a a u u =
        u * (Real.tanh (a * u) - a * u * pairedSech (a * u) ^ 2) / (4 * a)) ∧
    Filter.Tendsto
      (fun u : ℝ => pairedKhat a a u u / pairedP a a u u)
      Filter.atTop Filter.atTop

/-- The sharp pair-dependent entrywise escape identity and positivity. -/
def sharpPairDependentEntrywiseEscape : Prop :=
  ∀ a b : ℝ, (1 / 2 : ℝ) < a → (1 / 2 : ℝ) < b →
    ∀ u v : ℝ,
      pairedEscapePolynomial a b (pairedA (pairedKhat a b) u v) =
          a * b * pairedP a b u v ∧
        0 < a * b * pairedP a b u v

end

end MathlibPlus.Open.Analysis
