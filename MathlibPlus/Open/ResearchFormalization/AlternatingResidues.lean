import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization
namespace AlternatingResidues

noncomputable section

/-- U and V from the exact Vandermonde factorization in the packet. -/
def poleU (k : ℕ) (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a j => (x j) ^ (-(a.val : ℤ))

def poleV (k : ℕ) (x : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun b j => (x j) ^ (b.val : ℕ)

def poleMatrix (k : ℕ) (x c : Fin k → ℝ) (r : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  poleU k x * Matrix.diagonal (fun j => c j * (x j) ^ (r : ℤ)) *
    (poleV k x).transpose

/-- Claim 7958: ordered positive poles and alternating residues force positivity. -/
def claim7958 : Prop :=
  ∀ (k : ℕ) (x c : Fin k → ℝ),
    (∀ i, 0 < x i) →
    (∀ i j, i.val < j.val → x j < x i) →
    (∀ j, Real.sign (c j) = (-1 : ℝ) ^ j.val) →
    ∀ r : ℕ, 0 < Matrix.det (poleMatrix k x c r)

def mixedShellPolynomial : Polynomial ℝ :=
  (1 + (Polynomial.C 2) * Polynomial.X) *
    (1 + Polynomial.X) *
    (1 + Polynomial.X + Polynomial.X ^ 2) *
    (1 + Polynomial.C (9 / 10 : ℝ) * Polynomial.X)

def mixedShellPolynomialMinus : Polynomial ℝ :=
  (1 - (Polynomial.C 2) * Polynomial.X) *
    (1 - Polynomial.X) *
    (1 - Polynomial.X + Polynomial.X ^ 2) *
    (1 - Polynomial.C (9 / 10 : ℝ) * Polynomial.X)

def mixedShellCoefficients : Fin 6 → ℝ :=
  ![1, 49 / 10, 48 / 5, 52 / 5, 13 / 2, 9 / 5]

def mixedShellComplexPolynomial (z : ℂ) : ℂ :=
  Polynomial.eval z
    (mixedShellPolynomial.map (algebraMap ℝ ℂ))

def mixedShellReciprocalCoeff (n : ℕ) : ℝ :=
  PowerSeries.coeff n
    (PowerSeries.inv (Polynomial.toPowerSeries mixedShellPolynomialMinus))

def mixedShellDeterminant (r : ℕ) : ℝ :=
  let n := r - 1
  mixedShellReciprocalCoeff (n + 1) ^ 2 -
    mixedShellReciprocalCoeff n * mixedShellReciprocalCoeff (n + 2)

/-- Claim 7978: the stated positive polynomial has the mixed shell pattern and
its two-by-two minors remain positive. -/
def claim7978 : Prop :=
  (∀ i : Fin 6,
    Polynomial.coeff mixedShellPolynomial i = mixedShellCoefficients i ∧
      0 < mixedShellCoefficients i) ∧
  (∀ t : ℂ,
    mixedShellComplexPolynomial (-t) = 0 ↔
      t = (1 / 2 : ℂ) ∨
      t = 1 ∨
      t = Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ)) ∨
      t = Complex.exp (-Complex.I * ((Real.pi / 3 : ℝ) : ℂ)) ∨
      t = (10 / 9 : ℂ)) ∧
  (‖(1 / 2 : ℂ)‖ < ‖(1 : ℂ)‖ ∧
    ‖Complex.exp (Complex.I * ((Real.pi / 3 : ℝ) : ℂ))‖ = 1 ∧
    ‖Complex.exp (-Complex.I * ((Real.pi / 3 : ℝ) : ℂ))‖ = 1 ∧
    ‖(1 : ℂ)‖ < ‖(10 / 9 : ℂ)‖) ∧
  (∀ r : ℕ, 1 ≤ r → 0 < mixedShellDeterminant r)

end

end AlternatingResidues
end ResearchFormalization
end Open
end MathlibPlus
