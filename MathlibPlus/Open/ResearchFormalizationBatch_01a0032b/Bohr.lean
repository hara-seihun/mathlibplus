import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Batch_01a0032b

noncomputable section
open Classical
local instance bohrPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def bohrQ : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
    (Real.log 2 : ℂ) / (Real.log 3 : ℂ))

def bohrR : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi : ℂ) *
    (Real.log 3 : ℂ) / (Real.log 2 : ℂ))

def exponentialBasePower (b : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  Complex.exp (-(n : ℂ) * w * (Real.log b : ℂ))

def smallDivisorTerm (base : ℝ) (root : ℂ) (k : ℕ) (n : ℕ) (w : ℂ) : ℂ :=
  if 1 ≤ n then
    -((-(n : ℂ) * (Real.log base : ℂ)) ^ k * exponentialBasePower base w n) /
      ((n : ℂ) * (1 - root ^ n))
  else 0

def bohrU (w : ℂ) : ℂ :=
  ∑' n : ℕ, smallDivisorTerm 16 bohrQ 0 n w +
    ∑' n : ℕ, smallDivisorTerm 81 bohrR 0 n w

def bohrE (w : ℂ) : ℂ := Complex.exp (bohrU w)

def rightHalfPlane : Set ℂ := {w : ℂ | 1 / 4 < w.re}

def locallyUniformNatSeries (term : ℕ → ℂ → ℂ) (domain : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ domain →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ M : ℕ, N ≤ M → ∀ w ∈ K,
        ‖(Finset.range M).sum (fun n => term n w) -
          (Finset.range N).sum (fun n => term n w)‖ < ε

/-- Claim 10068: the elementary two-prime small-divisor bounds. -/
def elementaryTwoPrimeSmallDivisorBounds : Prop :=
  ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 < C₃ ∧
    (∀ n : ℕ, 1 ≤ n → ‖1 - bohrQ ^ n‖⁻¹ ≤ C₂ * 2 ^ n) ∧
    (∀ n : ℕ, 1 ≤ n → ‖1 - bohrR ^ n‖⁻¹ ≤ C₃ * 3 ^ n)

/-- Claim 10072: the rank-two logarithmic Bohr series, all fixed derivatives, and `E`. -/
def convergentRankTwoLogarithmicBohrSeries : Prop :=
  (∀ k : ℕ,
    locallyUniformNatSeries
      (fun n w => smallDivisorTerm 16 bohrQ k n w) rightHalfPlane ∧
    locallyUniformNatSeries
      (fun n w => smallDivisorTerm 81 bohrR k n w) rightHalfPlane) ∧
  DifferentiableOn ℂ bohrE rightHalfPlane ∧
  ∀ w : ℂ, w ∈ rightHalfPlane → bohrE w ≠ 0

/-- Claim 10073: the two exact irrational difference equations. -/
def exactIrrationalDifferenceEquations : Prop :=
  ∀ w : ℂ, w ∈ rightHalfPlane →
    let a : ℝ := 2 * Real.pi / Real.log 16
    let b : ℝ := 2 * Real.pi / Real.log 81
    bohrE (w - (b : ℂ) * Complex.I) =
        bohrE w / (1 - exponentialBasePower 16 w 1) ∧
    bohrE (w - (a : ℂ) * Complex.I) =
        bohrE w / (1 - exponentialBasePower 81 w 1)

end

end MathlibPlus.Open.Batch_01a0032b
