import Mathlib

noncomputable section

namespace MathlibPlus.Open.Exchangeable

open scoped BigOperators
open MeasureTheory

/-- The two signs used by the finite exchangeable model. -/
def signValue : Bool → ℝ
  | false => -1
  | true => 1

def priorDensity (y : ℝ) : ℝ := (15 / 16 : ℝ) * (1 - y ^ 2) ^ 2

def channelProbability (y : ℝ) (x : Bool) : ℝ :=
  (1 + (y / 2) * signValue x) / 2

def conditionalProductProbability {n : ℕ} (y : ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i, channelProbability y (x i)

def atomProbability {n : ℕ} (x : Fin n → Bool) : ℝ :=
  ∫ y in Set.Icc (-1 : ℝ) 1, priorDensity y * conditionalProductProbability y x

def plusCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i).card

def twoInversePower (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n

def closedFormAtomProbability {n : ℕ} (x : Fin n → Bool) : ℝ :=
  twoInversePower n *
    ∫ y in Set.Icc (-1 : ℝ) 1,
      priorDensity y * (1 + y / 2) ^ plusCount x *
        (1 - y / 2) ^ (n - plusCount x)

def normalizedSum (n : ℕ) : ℝ :=
  ∑ x : Fin n → Bool, atomProbability x

def zValue {n : ℕ} (x : Fin n → Bool) : ℝ :=
  (∑ i, signValue (x i)) / (n : ℝ)

def rationalReal (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

/-- Claim 45825: the displayed density, channel, rational atom formula, moments,
positivity, and normalization all hold on every finite cube. -/
def finite_rational_exchangeable_law : Prop :=
  (Function.Injective signValue) ∧
  (∀ n : ℕ, 2 ≤ n →
    (∫ y in Set.Icc (-1 : ℝ) 1, priorDensity y = 1) ∧
    (∀ y : ℝ, y ∈ Set.Icc (-1 : ℝ) 1 →
      (∀ x : Bool, 0 ≤ channelProbability y x) ∧
      (∑ x : Bool, channelProbability y x = 1)) ∧
    (∀ x : Fin n → Bool, atomProbability x = closedFormAtomProbability x) ∧
    (∀ x : Fin n → Bool, rationalReal (atomProbability x)) ∧
    (∀ x : Fin n → Bool, 0 ≤ atomProbability x) ∧
    normalizedSum n = 1 ∧
    (∀ j : ℕ,
      (∫ y in Set.Icc (-1 : ℝ) 1, y ^ (2 * j) * priorDensity y =
        (15 : ℝ) / (((2 * j + 1) * (2 * j + 3) * (2 * j + 5) : ℕ))) ∧
      (∫ y in Set.Icc (-1 : ℝ) 1, y ^ (2 * j + 1) * priorDensity y = 0)))

end MathlibPlus.Open.Exchangeable
