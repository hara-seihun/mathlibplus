import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

/-- The finite-prefix counterfeit polynomial, evaluated as a complex function. -/
def counterfeitPolynomial (K : ℕ) (B : ℝ) (z : ℂ) : ℂ :=
  (Finset.prod (Finset.Icc 1 (K + 1)) (fun j => 1 + z / (j : ℂ))) *
    (1 + ((2 * B / (B ^ 2 + 1) : ℝ) : ℂ) * z +
      ((1 / (B ^ 2 + 1) : ℝ) : ℂ) * z ^ 2)

def counterfeitDenominatorZero (K : ℕ) (B : ℝ) (t : ℂ) : Prop :=
  counterfeitPolynomial K B (-t) = 0

def listedCounterfeitPole (K : ℕ) (B : ℝ) (t : ℂ) : Prop :=
  (∃ j : ℕ, 1 ≤ j ∧ j ≤ K + 1 ∧ t = (j : ℂ)) ∨
    t = (B : ℂ) + Complex.I ∨ t = (B : ℂ) - Complex.I

def contourRadius (k : ℕ) : ℝ :=
  (k : ℝ) + 1 / 2

def positivePrefixContour (K k : ℕ) (B : ℝ) : Prop :=
  k ≤ K ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ K + 1 →
      (‖(j : ℂ)‖ < contourRadius k ↔ j ≤ k)) ∧
    ‖(B : ℂ) + Complex.I‖ > contourRadius k ∧
    ‖(B : ℂ) - Complex.I‖ > contourRadius k

def basePoleAmplitude (K j : ℕ) : ℝ :=
  Finset.prod ((Finset.Icc 1 (K + 1)).filter (fun l => l ≠ j))
    (fun l => (1 - (j : ℝ) / (l : ℝ))⁻¹)

def modifiedPoleAmplitude (K : ℕ) (B : ℝ) (j : ℕ) : ℝ :=
  basePoleAmplitude K j * ((B ^ 2 + 1) / ((B - j) ^ 2 + 1))

/-- Explicit false-real-rooted counterfeits pass every fixed finite prefix. -/
def claim_8067 : Prop :=
  ∀ K : ℕ, ∀ B : ℝ, K + 1 < B →
    counterfeitPolynomial K B 0 = 1 ∧
    counterfeitPolynomial K B ((-B : ℂ) + Complex.I) = 0 ∧
    (((-B : ℂ) + Complex.I).im ≠ 0) ∧
    (∀ t : ℂ,
      counterfeitDenominatorZero K B t ↔ listedCounterfeitPole K B t) ∧
    (∀ k : ℕ, k ≤ K → positivePrefixContour K k B) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ K + 1 →
      modifiedPoleAmplitude K B j =
          basePoleAmplitude K j * ((B ^ 2 + 1) / ((B - j) ^ 2 + 1)) ∧
      0 < (B ^ 2 + 1) / ((B - j) ^ 2 + 1) ∧
      0 < ((-1 : ℝ) ^ (j - 1)) * modifiedPoleAmplitude K B j)

end
end MathlibPlus.Open.Research
