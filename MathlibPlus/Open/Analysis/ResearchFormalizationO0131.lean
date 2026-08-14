import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The cut used by the finite-frequency Stieltjes statements. -/
def offStieltjesCut (u : ℂ) : Prop :=
  ¬ (u.im = 0 ∧ u.re ≤ (1 / 4 : ℝ))

/-- The two squared variables in the finite-frequency impedance. -/
def qPlus (t : ℝ) (z : ℂ) : ℂ :=
  (z + Complex.I * (t : ℂ)) ^ 2 / z

def qMinus (t : ℝ) (z : ℂ) : ℂ :=
  (z - Complex.I * (t : ℂ)) ^ 2 / z

def impedanceNumerator (E : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  E (qPlus t z) - E (qMinus t z)

def impedanceDenominator (E : ℂ → ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  E (qPlus t z) + E (qMinus t z)

/-- A real-variable formulation of an error term `O(t^p)` at zero. -/
def realBigOAtZero (r : ℝ → ℂ) (p : ℕ) : Prop :=
  ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ t : ℝ, 0 < |t| → |t| < δ → ‖r t‖ ≤ C * |t| ^ p

/--
A generic simple zero off the Stieltjes cut gives the asserted nearby
finite-frequency impedance pole, including the displayed asymptotics.
-/
def genericSimpleOffCutZeroPersistence : Prop :=
  ∀ (E : ℂ → ℂ) (u₀ : ℂ),
    Differentiable ℂ E →
    E u₀ = 0 →
    deriv E u₀ ≠ 0 →
    offStieltjesCut u₀ →
    ∃ u : ℝ → ℂ,
      realBigOAtZero
        (fun t ↦
          u t -
            (u₀ +
              (1 / u₀ + 2 * deriv (deriv E) u₀ / deriv E u₀) * (t : ℂ) ^ 2)) 4 ∧
      realBigOAtZero
        (fun t ↦
          impedanceNumerator E t (u t) -
            4 * Complex.I * (t : ℂ) * deriv E u₀) 3 ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ t : ℝ, 0 < |t| → |t| < δ →
          impedanceDenominator E t (u t) = 0 ∧
          impedanceNumerator E t (u t) ≠ 0 ∧
          (u t).im ≠ 0

end

end MathlibPlus.Open.Analysis
