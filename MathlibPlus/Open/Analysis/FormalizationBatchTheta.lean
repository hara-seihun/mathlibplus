import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatchTheta

open Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

/-- The summand `x_n(t)` in the theta packet. -/
def xTerm (n : ℕ) (t : ℝ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * t)

def phiBase (t : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n then
      2 * Real.exp (t / 2) * xTerm n t * (2 * xTerm n t - 3) *
        Real.exp (-xTerm n t)
    else 0

/-- Even extension of the theta expression. -/
def Phi (t : ℝ) : ℝ := phiBase |t|

def thetaPrimitive (t : ℝ) : ℝ :=
  Real.exp (t / 2) *
    ∑' n : ℕ, if 1 ≤ n then Real.exp (-xTerm n t) else 0

def correlation (y x : ℝ) : ℂ :=
  ∫ d : ℝ,
    ((Phi (y + d) * Phi (y - d) : ℝ) : ℂ) *
      Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ))

def divisorCharacter (x : ℝ) (k : ℕ) : ℂ :=
  Finset.sum (Nat.divisors k) (fun d =>
    Complex.exp
      ((-Complex.I * (x : ℂ)) *
        Real.log ((d : ℝ) / ((k / d : ℕ) : ℝ))))

def divisorSigma (z : ℂ) (k : ℕ) : ℂ :=
  Finset.sum (Nat.divisors k) (fun d => Complex.exp (z * Real.log (d : ℝ)))

def complexNatPower (z : ℂ) (k : ℕ) : ℂ :=
  Complex.exp (z * Real.log (k : ℝ))

def claim_13698 : Prop :=
  (∀ y x : ℝ,
    correlation y x =
      ∫ d : ℝ,
        ((Phi (y + d) * Phi (y - d) : ℝ) : ℂ) *
          Complex.exp (2 * Complex.I * (x : ℂ) * (d : ℂ))) ∧
    (∀ x : ℝ, ∀ k : ℕ, 1 ≤ k →
      divisorCharacter x k =
        complexNatPower (Complex.I * (x : ℂ)) k *
          divisorSigma (-2 * Complex.I * (x : ℂ)) k)


def claim_13703 : Prop :=
  (∀ t : ℝ,
    thetaPrimitive (-t) = thetaPrimitive t + Real.sinh (t / 2)) ∧
    (∀ t : ℝ,
      iteratedDeriv 2 thetaPrimitive t - (1 / 4) * thetaPrimitive t = Phi t)


def rho (t : ℝ) : ℝ := Real.exp (-t / 2) / 2 - thetaPrimitive t

def claim_13713 : Prop :=
  (∀ t : ℝ, rho (-t) = rho t) ∧
    (∀ t : ℝ, 0 < rho t) ∧
    (∀ t : ℝ,
      -(iteratedDeriv 2 rho t) + (1 / 4) * rho t = Phi t) ∧
    (∃ C R : ℝ, 0 ≤ C ∧ 0 ≤ R ∧
      ∀ t : ℝ, R ≤ |t| → |rho t| ≤ C * Real.exp (-|t| / 2))


def dirichletTerm (x : ℝ) (s : ℂ) (k : ℕ) : ℂ :=
  if 1 ≤ k then
    divisorCharacter x k * Complex.exp (-s * Real.log (k : ℝ))
  else 0

def claim_13715 : Prop :=
  ∀ x : ℝ, ∃ R : ℝ, ∀ s : ℂ, R < s.re →
    Summable (dirichletTerm x s) ∧
      ∑' k : ℕ, dirichletTerm x s k =
        riemannZeta (s + Complex.I * (x : ℂ)) *
          riemannZeta (s - Complex.I * (x : ℂ))


def P (x lam : ℝ) : ℝ :=
  ((lam + 1 / 2) ^ 2 + x ^ 2) * ((lam - 1 / 2) ^ 2 + x ^ 2)

def Pprime (x lam : ℝ) : ℝ := 4 * lam * (lam ^ 2 + x ^ 2 - 1 / 4)

def LOperator (x : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  iteratedDeriv 4 f u + (2 * x ^ 2 - 1 / 2) * iteratedDeriv 2 f u +
    (x ^ 2 + 1 / 4) ^ 2 * f u

def hyperbolicWave (ω u : ℝ) : ℝ := u * Real.cosh (ω * u)

def claim_13719 : Prop :=
  (∀ x lam : ℝ, Pprime x lam = deriv (P x) lam) ∧
    (∀ x ω u : ℝ,
      LOperator x (hyperbolicWave ω) u =
        P x ω * hyperbolicWave ω u + Pprime x ω * Real.sinh (ω * u)) ∧
    Pprime 0 (1 / 4) < 0 ∧ 0 < Pprime 0 1


def finiteS (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun m n =>
    Finset.sum (Finset.Icc 1 N) (fun k =>
      if n.1 + 1 = (m.1 + 1) * k ^ 2 then (k : ℚ)⁻¹ else 0)

def finiteM (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun m n =>
    Finset.sum (Finset.Icc 1 N) (fun k =>
      if n.1 + 1 = (m.1 + 1) * k ^ 2 then
        ((ArithmeticFunction.moebius k : ℤ) : ℚ) / (k : ℚ)
      else 0)

def claim_13722 : Prop :=
  ∀ N : ℕ,
    finiteM N * finiteS N = (1 : Matrix (Fin N) (Fin N) ℚ) ∧
      finiteS N * finiteM N = (1 : Matrix (Fin N) (Fin N) ℚ)

end

end MathlibPlus.Open.Analysis.FormalizationBatchTheta
