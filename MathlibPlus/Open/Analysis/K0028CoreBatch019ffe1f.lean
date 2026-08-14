import Mathlib

noncomputable section

open scoped BigOperators
open UpperHalfPlane

namespace MathlibPlus.Open.Analysis.K0028CoreBatch019ffe1f

/-- The real Gamma factor in the completed zeta function. -/
def gammaR (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) * Complex.Gamma (s / 2)

/-- The completed zeta factor used by the boundary state. -/
def completedLambda (s : ℂ) : ℂ := gammaR s * riemannZeta s

def eisensteinConstantTerm (y : ℝ) (s : ℂ) : ℂ :=
  completedLambda (2 * s) * (y : ℂ) ^ s +
    completedLambda (2 * s - 1) * (y : ℂ) ^ (1 - s)

def incomingCoefficient (s : ℂ) : ℂ :=
  completedLambda s * completedLambda (2 * s)

def outgoingCoefficient (s : ℂ) : ℂ :=
  completedLambda s * completedLambda (2 * s - 1)

def evenBoundaryCoefficient (s : ℂ) : ℂ :=
  (incomingCoefficient s + outgoingCoefficient s) / 2

def oddBoundaryCoefficient (s : ℂ) : ℂ :=
  -(Complex.I / 2) * (incomingCoefficient s - outgoingCoefficient s)

/-- Claim 7713: the completed Eisenstein constant term, its incoming and
outgoing coefficients, and the even/odd fixed-point ports. -/
def claim7713 : Prop :=
  (∀ (y : ℝ) (s : ℂ), 0 < y →
    eisensteinConstantTerm y s =
      completedLambda (2 * s) * (y : ℂ) ^ s +
        completedLambda (2 * s - 1) * (y : ℂ) ^ (1 - s)) ∧
    (∀ (t : ℝ),
      let s := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
      outgoingCoefficient s = star (incomingCoefficient s) ∧
        eisensteinConstantTerm 1 s = 2 * evenBoundaryCoefficient s ∧
        (deriv (fun y : ℝ => eisensteinConstantTerm y s) 1 -
            (1 / 2 : ℂ) * eisensteinConstantTerm 1 s) =
          -(2 * (t : ℂ)) * oddBoundaryCoefficient s)

open ModularForm

/-- The level-one Eisenstein series used in the Niemeier identities. -/
def E4fun : ℍ → ℂ := fun z => ModularForm.E (by norm_num : 3 ≤ (4 : ℕ)) z
def E12fun : ℍ → ℂ := fun z => ModularForm.E (by norm_num : 3 ≤ (12 : ℕ)) z
def E14fun : ℍ → ℂ := fun z => ModularForm.E (by norm_num : 3 ≤ (14 : ℕ)) z
def Deltafun : ℍ → ℂ := fun z => CuspForm.discriminant z

def thetaH (h : ℕ) (z : ℍ) : ℂ :=
  E4fun z ^ 3 + ((24 : ℂ) * (h : ℂ) - 720) * Deltafun z

def serreJet (k : ℕ) (F : ℍ → ℂ) : ℍ → ℂ :=
  fun z => Derivative.serreDerivative (k : ℂ) F z

def F16fun (h : ℕ) : ℍ → ℂ :=
  serreJet 14 (serreJet 12 (thetaH h))

/-- Claim 7715: the exact Niemeier theta formula and the two Serre-jet
identities, stated on the upstream level-one modular-form carriers. -/
def claim7715 : Prop :=
  ∀ (h : ℕ) (z : ℍ),
    thetaH h z =
        E4fun z ^ 3 + ((24 : ℂ) * (h : ℂ) - 720) * Deltafun z ∧
      serreJet 12 (thetaH h) z = -E14fun z ∧
      F16fun h z =
        (7 / 6 : ℂ) * E4fun z ^ 4 - 1152 * E4fun z * Deltafun z

end MathlibPlus.Open.Analysis.K0028CoreBatch019ffe1f
