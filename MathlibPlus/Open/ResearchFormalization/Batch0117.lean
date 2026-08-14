import Mathlib

open scoped BigOperators
open MeasureTheory
noncomputable section
namespace MathlibPlus.Open.ResearchFormalization.Batch0117

/-- The exact local logarithmic derivative in the admitted rank-one claim. -/
def localLogDerivative (p : ℕ) (χp s : ℂ) : ℂ :=
  -deriv (fun z : ℂ =>
    Complex.log ((1 - χp * Complex.cpow (p : ℂ) (-z))⁻¹)) s

def localPrimePowerSum (p : ℕ) (χp s : ℂ) : ℂ :=
  ∑' m : ℕ,
    if 1 ≤ m then
      (Real.log (p : ℝ) : ℂ) * χp ^ m *
        Complex.cpow (p : ℂ) (-((m : ℂ) * s))
    else 0

/-- Claim 12264: exact local logarithmic-derivative prime-power expansion. -/
def claim12264 : Prop :=
  ∀ (p : ℕ) (χp s : ℂ), Nat.Prime p →
    ‖χp * Complex.cpow (p : ℂ) (-s)‖ < 1 →
      localLogDerivative p χp s = localPrimePowerSum p χp s

/-- The two polynomial presentations in the admitted Fitting-divisor claim. -/
abbrev polynomialRing := Polynomial ℂ
abbrev polynomialPair := Fin 2 → polynomialRing

def presentationA : Matrix (Fin 2) (Fin 2) polynomialRing :=
  !![Polynomial.X, 0; 0, Polynomial.X]
def presentationB : Matrix (Fin 2) (Fin 2) polynomialRing :=
  !![Polynomial.X, 1; 0, Polynomial.X]

abbrev cokerA : Type :=
  polynomialPair ⧸ (Matrix.toLin' presentationA).range
abbrev cokerB : Type :=
  polynomialPair ⧸ (Matrix.toLin' presentationB).range

instance cokerAComplexModule : Module ℂ cokerA :=
  Module.restrictScalars ℂ polynomialRing cokerA
instance cokerBComplexModule : Module ℂ cokerB :=
  Module.restrictScalars ℂ polynomialRing cokerB

def idealAtZero : Ideal polynomialRing := Ideal.span {Polynomial.X}
def idealAtZeroSquared : Ideal polynomialRing :=
  Ideal.span {Polynomial.X ^ 2}

def fiberSubmodule (M : Type) [AddCommGroup M] [Module polynomialRing M]
    [Module ℂ M] : Submodule ℂ M :=
  Submodule.span ℂ (Set.range
    (fun m : M => (Polynomial.X : polynomialRing) • m))

abbrev fiber (M : Type) [AddCommGroup M] [Module polynomialRing M]
    [Module ℂ M] : Type := M ⧸ fiberSubmodule M

/-- Claim 12267: equal Fitting determinants can hide different local modules. -/
def claim12267 : Prop :=
  Matrix.det presentationA = Polynomial.X ^ 2 ∧
    Matrix.det presentationB = Polynomial.X ^ 2 ∧
    Nonempty (cokerA ≃ₗ[polynomialRing]
      (Fin 2 → (polynomialRing ⧸ idealAtZero))) ∧
    Nonempty (cokerB ≃ₗ[polynomialRing]
      (polynomialRing ⧸ idealAtZeroSquared)) ∧
    Module.finrank ℂ (fiber cokerA) = 2 ∧
    Module.finrank ℂ (fiber cokerB) = 1

/-- The diagonal off-axis block and the split Hermitian pairing. -/
def offAxisBlock : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun i : Fin 4 =>
    if i = 0 then 1 + 2 * Complex.I
    else if i = 1 then -1 + 2 * Complex.I
    else if i = 2 then 1 - 2 * Complex.I
    else -1 - 2 * Complex.I)

def splitPairing : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]

def splitSkewAdjoint (A J : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  A.conjTranspose * J + J * A = 0

def splitInertia22 (J : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ P : Matrix (Fin 4) (Fin 4) ℂ,
    Matrix.det P ≠ 0 ∧
      P.conjTranspose * J * P =
        !![1, 0, 0, 0;
           0, 1, 0, 0;
           0, 0, -1, 0;
           0, 0, 0, -1]

def offAxisCharacteristic : Polynomial ℂ :=
  Polynomial.C 25 + Polynomial.C 6 * Polynomial.X ^ 2 + Polynomial.X ^ 4

/-- Claim 12268: explicit self-dual off-axis block. -/
def claim12268 : Prop :=
  splitSkewAdjoint offAxisBlock splitPairing ∧
    Matrix.charpoly offAxisBlock = offAxisCharacteristic ∧
    (∀ z : ℂ, Polynomial.eval z offAxisCharacteristic = 0 →
      z.re = 1 ∨ z.re = -1) ∧
    splitInertia22 splitPairing

end MathlibPlus.Open.ResearchFormalization.Batch0117
