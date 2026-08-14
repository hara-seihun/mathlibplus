import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/-- The exponential scale appearing in the positive-side Riemann-theta atoms. -/
def thetaX (n : ℕ) (t : ℝ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * t)

/-- A positive-side theta atom. -/
def thetaAtom (n : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp (t / 2) * thetaX n t * (2 * thetaX n t - 3) *
    Real.exp (-thetaX n t)

/-- The positive-side sum of theta atoms. -/
def thetaPositive (t : ℝ) : ℝ :=
  ∑' n : ℕ, if 0 < n then thetaAtom n t else 0

/-- The even extension of the positive-side source. -/
def thetaPhi (t : ℝ) : ℝ := thetaPositive |t|

/-- The primitive used by the modular and differential identities. -/
def thetaG (t : ℝ) : ℝ :=
  Real.exp (t / 2) *
    ∑' n : ℕ,
      if 0 < n then
        Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * t)))
      else 0

/-- The correlation at frequency `z`; the source writes this as `C_y(z)`. -/
def thetaCorrelation (y z : ℝ) : ℂ :=
  ∫ d : ℝ,
    (thetaPhi (y + d) : ℂ) * (thetaPhi (y - d) : ℂ) *
      Complex.exp (Complex.I * (z * d))

/--
The admitted Riemann-theta source and correlation statement.  The modular
identity and the differential identity are included as the exact repair
context that supplies the global even extension.
-/
def riemannThetaSourceAndCorrelation : Prop :=
  (∀ (n : ℕ) (t : ℝ),
    thetaX n t = Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * t)) ∧
  (∀ (n : ℕ) (t : ℝ),
    thetaAtom n t =
      2 * Real.exp (t / 2) * thetaX n t * (2 * thetaX n t - 3) *
        Real.exp (-thetaX n t)) ∧
  (∀ t : ℝ, thetaPhi (-t) = thetaPhi t) ∧
  (∀ t : ℝ, thetaG (-t) = thetaG t + Real.sinh (t / 2)) ∧
  (∀ t : ℝ,
    deriv (fun s : ℝ => deriv thetaG s) t - (1 / 4 : ℝ) * thetaG t =
      thetaPhi t) ∧
  (∀ (y x : ℝ),
    thetaCorrelation y (2 * x) =
      ∫ d : ℝ,
        (thetaPhi (y + d) : ℂ) * (thetaPhi (y - d) : ℂ) *
          Complex.exp (Complex.I * ((2 * x) * d)))

end MathlibPlus.Open.ResearchFormalization
