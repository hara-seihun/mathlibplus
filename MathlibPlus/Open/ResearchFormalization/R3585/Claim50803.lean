import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R3585.Claim50803

abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev PositiveIndex := {k : ℕ // 1 ≤ k}

/-- The reflected Euler atom on the centered complex carrier. -/
def reflectedAtom (lambda r : ℝ) (z : ℂ) : ℂ :=
  (1 + (r : ℂ) * Complex.exp ((lambda : ℂ) * z)) *
    (1 + (r : ℂ) * Complex.exp (-((lambda : ℂ) * z)))

/-- The positive-amplitude reflected power defect. -/
def reflectedPowerDefect (r : ℝ) (k : ℕ) : ℝ :=
  r ^ k + (r ^ k)⁻¹ - 2

/-- The literal Euler coefficient obtained after the centered substitution. -/
def literalEulerCoefficient (p : ℕ) (r : ℝ) (k : ℕ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * (-1 : ℂ) ^ k *
    (Real.rpow (p : ℝ) ((k : ℝ) / 2) : ℂ) *
      (reflectedPowerDefect r k : ℂ)

/-- The branch-independent logarithmic derivative, written as the difference
of the two quotient derivatives rather than as a principal complex logarithm. -/
def reflectedLogDerivative (lambda r : ℝ) (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => reflectedAtom lambda r w) z /
      reflectedAtom lambda r z -
    deriv (fun w : ℂ => reflectedAtom lambda 1 w) z /
      reflectedAtom lambda 1 z

/-- The all-order reflected coefficient series in the Laurent variable. -/
def reflectedEulerSeries (lambda r : ℝ) (x : ℂ) : ℂ :=
  ∑' k : PositiveIndex,
    (lambda : ℂ) * (-1 : ℂ) ^ k.1 *
      (reflectedPowerDefect r k.1 : ℂ) * x ^ k.1

/-- The exact all-order branch-independent expansion and literal prime-power
coefficient substitution for the reflected Euler atom. -/
def claim50803 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ (r : ℝ), 0 < r →
      ∀ (s : ℂ),
        let lambda : ℝ := Real.log (p : ℝ)
        let z : ℂ := s - (1 / 2 : ℂ)
        let x : ℂ := Complex.exp (-((lambda : ℂ) * z))
        (‖(r : ℂ) * x‖ < 1 ∧
            ‖(r : ℂ)⁻¹ * x‖ < 1) →
          reflectedLogDerivative lambda r z =
              reflectedEulerSeries lambda r x ∧
            ∀ k : PositiveIndex,
              x ^ k.1 =
                  (Real.rpow (p : ℝ) ((k.1 : ℝ) / 2) : ℂ) *
                    Complex.cpow ((p ^ k.1 : ℕ) : ℂ) (-s) ∧
                (lambda : ℂ) * (-1 : ℂ) ^ k.1 *
                    (reflectedPowerDefect r k.1 : ℂ) * x ^ k.1 =
                  literalEulerCoefficient p r k.1 *
                    Complex.cpow ((p ^ k.1 : ℕ) : ℂ) (-s)

end MathlibPlus.Open.ResearchFormalization.R3585.Claim50803

end
