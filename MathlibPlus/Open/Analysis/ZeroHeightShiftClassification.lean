import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The horizontal Laguerre curvature of a complex-valued function of real height. -/
def horizontalLaguerreCurvature (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (deriv f t) - (deriv (deriv f) t * star (f t)).re

/-- The Xi function on a vertical line. -/
def xiLine (σ t : ℝ) : ℂ :=
  completedRiemannZeta ((σ : ℂ) - (t : ℂ) * Complex.I)

/-- The normalized horizontal curvature of Xi. -/
def qXi (σ t : ℝ) : ℝ :=
  horizontalLaguerreCurvature (fun u : ℝ => xiLine σ u) t /
    Complex.normSq (xiLine σ t)

/-- The integer-shifted gamma carrier. -/
def integerShiftedGamma (m : ℕ) (s : ℂ) : ℂ :=
  Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma ((m : ℂ) + s / 2)

/-- The carrier obtained from Xi by the integer-shifted gamma normalization. -/
def integerShiftedCarrier (m : ℕ) (σ t : ℝ) : ℂ :=
  completedRiemannZeta ((σ : ℂ) - (t : ℂ) * Complex.I) /
    (‖integerShiftedGamma m ((σ : ℂ) - (t : ℂ) * Complex.I)‖ : ℂ)

/-- The trigamma function, as the derivative of the complex digamma function. -/
def psiOne (z : ℂ) : ℂ :=
  deriv Complex.digamma z

/-- The normalized zero-height carrier curvature. -/
def zeroHeightK (m : ℕ) (a : ℝ) : ℝ :=
  qXi (1 / 2 + a) 0 -
    (1 / 4 : ℝ) *
      (psiOne ((m : ℂ) + (1 / 4 : ℂ) + (a : ℂ) / 2)).re

/-- Complete classification of the fixed integer carriers at zero height. -/
def completeZeroHeightShiftClassification : Prop :=
  (∀ (m : ℕ), 1 ≤ m → ∀ a ∈ Set.Icc (0 : ℝ) (1 / 2),
    zeroHeightK m a =
      horizontalLaguerreCurvature
          (fun t : ℝ => integerShiftedCarrier m (1 / 2 + a) t) 0 /
        Complex.normSq (integerShiftedCarrier m (1 / 2 + a) 0)) ∧
  (∀ (m : ℕ), 1 ≤ m →
    StrictMonoOn (fun a : ℝ => zeroHeightK m a) (Set.Icc (0 : ℝ) (1 / 2))) ∧
  (∀ (m : ℕ), 6 ≤ m → ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
    0 < horizontalLaguerreCurvature
      (fun t : ℝ => integerShiftedCarrier m σ t) 0) ∧
  (∀ (m : ℕ), 1 ≤ m → m ≤ 5 →
    horizontalLaguerreCurvature
      (fun t : ℝ => integerShiftedCarrier m (1 / 2) t) 0 < 0)

/-- Positivity of a fixed integer carrier on the whole zero-height segment. -/
def zeroHeightPositive (m : ℕ) : Prop :=
  ∀ σ ∈ Set.Icc (1 / 2 : ℝ) 1,
    0 < horizontalLaguerreCurvature
      (fun t : ℝ => integerShiftedCarrier m σ t) 0

/-- Nonnegative carrier curvature throughout the open critical strip and all heights. -/
def globalCarrierNonnegative (m : ℕ) : Prop :=
  ∀ (σ t : ℝ), 1 / 2 < σ → σ < 1 →
    0 ≤ horizontalLaguerreCurvature
      (fun u : ℝ => integerShiftedCarrier m σ u) t

/-- Shift six is the least fixed integer carrier not excluded at zero height. -/
def shiftSixLeastFixedIntegerCarrier : Prop :=
  zeroHeightPositive 6 ∧
  (∀ m : ℕ, 1 ≤ m → zeroHeightPositive m → 6 ≤ m) ∧
  (∀ m : ℕ, 6 ≤ m → zeroHeightPositive m) ∧
  (∀ m : ℕ, 1 ≤ m → m < 6 → ¬ zeroHeightPositive m) ∧
  (∀ m : ℕ, 6 ≤ m → globalCarrierNonnegative m → RiemannHypothesis)

end

end MathlibPlus.Open.Analysis
