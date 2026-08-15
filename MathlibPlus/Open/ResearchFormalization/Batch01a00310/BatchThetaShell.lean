import Mathlib

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchThetaShell

def thetaY (u : ℝ) : ℝ := Real.pi * Real.exp (2 * u)

def thetaPhi (u : ℝ) : ℝ :=
  (4 * Real.pi^2 * Real.exp (9 * u / 2) -
      6 * Real.pi * Real.exp (5 * u / 2)) *
    Real.exp (-Real.pi * Real.exp (2 * u))

def thetaPhiAlt (u : ℝ) : ℝ :=
  2 * Real.rpow Real.pi (-1 / 4 : ℝ) *
    Real.rpow (thetaY u) (5 / 4 : ℝ) *
    (2 * thetaY u - 3) * Real.exp (-(thetaY u))

def claim13883 : Prop :=
  (∀ u : ℝ, thetaPhi u = thetaPhiAlt u) ∧
    ∀ u : ℝ, 0 ≤ u →
      0 < thetaPhi u ∧ Real.pi ≤ thetaY u ∧ (3 / 2 : ℝ) < thetaY u

def F1 (w : ℂ) : ℂ :=
  2 * integral (Measure.restrict volume (Set.Ici (0 : ℝ)))
    (fun u : ℝ =>
      Complex.ofReal (thetaPhi u) * Complex.cosh (w * (u : ℂ)))

def claim13884 : Prop :=
  Differentiable ℂ F1 ∧
    (∀ w : ℂ, F1 (-w) = F1 w) ∧
    ∃ A : ℂ → ℂ,
      Differentiable ℂ A ∧
      (∀ w : ℂ, F1 w = A (w^2)) ∧
      ∃ coeff : ℕ → ℝ,
        (∀ n : ℕ, 0 < coeff n) ∧
        ∀ w : ℂ,
          HasSum (fun n : ℕ => Complex.ofReal (coeff n) * w^n) (A w)

def roucheCenter : ℂ :=
  (2.697151842339519632505936434737308603769 : ℝ) +
    (20.62534600592171760132994578980489712729 : ℝ) * Complex.I

def roucheRadius : ℝ := (10 : ℝ)^(-20 : ℤ)

def roucheDisk : Set ℂ := {w | ‖w - roucheCenter‖ < roucheRadius}

def claim13886 : Prop :=
  ∃! w : ℂ, w ∈ roucheDisk ∧ F1 w = 0

def firstDerivativeF1 (w : ℂ) : ℂ := deriv F1 w

def secondDerivativeF1 (w : ℂ) : ℂ := deriv (deriv F1) w

def claim13887 : Prop :=
  ‖F1 roucheCenter‖ +
      (1 / 2 : ℝ) *
        sSup (Set.image (fun w : ℂ => ‖secondDerivativeF1 w‖) roucheDisk) *
        roucheRadius^2 <
    (8.40 : ℝ) * (10 : ℝ)^(-41 : ℤ) ∧
  ‖firstDerivativeF1 roucheCenter‖ * roucheRadius >
    (9.22 : ℝ) * (10 : ℝ)^(-25 : ℤ)

end MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchThetaShell
