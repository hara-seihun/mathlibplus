import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim28997

abbrev F7 := ZMod 7

structure QuadraticParameters where
  alpha : F7
  beta : F7
  epsilon : F7
  deriving DecidableEq, Fintype

structure VoltageRow where
  b : F7 → F7
  c : F7 → F7
  t : F7 → F7
  deriving DecidableEq, Fintype

def quadraticVoltageRow (p : QuadraticParameters) : VoltageRow :=
  { b := fun x => p.alpha * x + p.beta * x ^ 2
    c := fun x => (3 * p.alpha + 2 * p.epsilon) * x + 6 * p.beta * x ^ 2
    t := fun x => p.epsilon * x + 2 * p.beta * x ^ 2 }

def nonlinearVoltageRows : Set VoltageRow :=
  {row | ∃ p : QuadraticParameters, p.beta ≠ 0 ∧ row = quadraticVoltageRow p}

def commonFiberShape : Set F7 := {0, 1, 3}

def translatedFiberSection (t : F7 → F7) : Set (F7 × F7) :=
  {p | ∃ s : F7, s ∈ commonFiberShape ∧ p.2 = t p.1 + s}

def aperiodicTranslatedFiberSection (S : Set (F7 × F7)) : Prop :=
  ∀ v : F7 × F7,
    (∀ p : F7 × F7, p ∈ S ↔ p + v ∈ S) → v = 0

/-- Claim 28997: the 294 nonlinear quadratic voltage rows with common shape
`{0,1,3}` produce aperiodic translated-fiber sections of size 21. -/
def claim28997 : Prop :=
  Set.ncard nonlinearVoltageRows = 294 ∧
    ∀ row : VoltageRow, row ∈ nonlinearVoltageRows →
      (translatedFiberSection row.t).ncard = 21 ∧
        aperiodicTranslatedFiberSection (translatedFiberSection row.t)

end MathlibPlus.Open.ResearchFormalization.Claim28997
