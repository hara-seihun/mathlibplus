import Mathlib

namespace MathlibPlus.Open.Analysis.Claim42858

/-- The concrete polynomial multiplier family. -/
noncomputable def escapingMultiplierPolynomial (n : ℕ) : Polynomial ℂ :=
  1 + Polynomial.C (1 / (((n + 1 : ℕ) : ℂ) ^ 2)) * Polynomial.X ^ 2

noncomputable def escapingMultiplier (n : ℕ) (z : ℂ) : ℂ :=
  (escapingMultiplierPolynomial n).eval z

def escapingRadius (n : ℕ) : ℝ := n + 1

def escapingPointPlus (n : ℕ) : ℂ :=
  Complex.I * (escapingRadius n : ℂ)

def escapingPointMinus (n : ℕ) : ℂ :=
  -Complex.I * (escapingRadius n : ℂ)

/-- Compact-open convergence of the concrete polynomial family together with
its exact nonreal zero pair and escaping moduli. -/
def claim42858_compactOpenDoesNotImplyDivisorTightness : Prop :=
  (∀ n : ℕ, ∀ z : ℂ,
    escapingMultiplier n z =
      (escapingMultiplierPolynomial n).eval z) ∧
  (∀ n : ℕ,
    0 < escapingRadius n ∧
    escapingMultiplier n (escapingPointPlus n) = 0 ∧
    escapingMultiplier n (escapingPointMinus n) = 0 ∧
    (escapingPointPlus n).im = escapingRadius n ∧
    (escapingPointMinus n).im = -escapingRadius n ∧
    ‖escapingPointPlus n‖ = escapingRadius n ∧
    ‖escapingPointMinus n‖ = escapingRadius n) ∧
  (∀ R : ℝ, 0 ≤ R →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ,
        ‖z‖ ≤ R → ‖escapingMultiplier n z - 1‖ < ε)

end MathlibPlus.Open.Analysis.Claim42858
