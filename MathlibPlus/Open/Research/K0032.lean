import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.K0032

open Complex

/-- The completed real gamma factor used by the two completed zeta products. -/
def gammaR (s : ℂ) : ℂ := Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (s / 2)

def completedLambda (s : ℂ) : ℂ := gammaR s * riemannZeta s

def zetaZeroPlus (s : ℂ) : ℂ := completedLambda s * completedLambda (2 * s)

def zetaZeroMinus (s : ℂ) : ℂ := completedLambda s * completedLambda (2 * s - 1)

def claim7735 : Prop :=
  (∀ s : ℂ, gammaR s = Complex.cpow (Real.pi : ℂ) (-s / 2) * Complex.Gamma (s / 2)) ∧
  (∀ s : ℂ, completedLambda s = gammaR s * riemannZeta s) ∧
  (∀ s : ℂ, zetaZeroPlus s = completedLambda s * completedLambda (2 * s)) ∧
  (∀ s : ℂ, zetaZeroMinus s = completedLambda s * completedLambda (2 * s - 1))

def realType (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, f (star s) = star (f s)

def completedFunctionalEquation (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, f s = f (1 - s)

def zetaZeroEven (s : ℂ) : ℂ := (zetaZeroPlus s).re

def zetaZeroOdd (s : ℂ) : ℂ := (zetaZeroPlus s).im

def claim7738 : Prop :=
  ∀ t : ℝ,
    realType completedLambda →
    completedFunctionalEquation completedLambda →
      zetaZeroMinus (1 / 2 + (t : ℂ) * I) =
          star (zetaZeroPlus (1 / 2 + (t : ℂ) * I)) ∧
        zetaZeroEven (1 / 2 + (t : ℂ) * I) =
          (zetaZeroPlus (1 / 2 + (t : ℂ) * I)).re ∧
        zetaZeroOdd (1 / 2 + (t : ℂ) * I) =
          (zetaZeroPlus (1 / 2 + (t : ℂ) * I)).im

end MathlibPlus.Open.Research.K0032
