import Mathlib

namespace MathlibPlus.Open.ResearchFormalization
namespace MarkerCycle

noncomputable section

abbrev Coeff := MvPolynomial ℕ ℚ

 def x (n : ℕ) : Coeff := MvPolynomial.X n

/-- The marker transform sends the coefficient of z^r to multiplication by x_(r+s). -/
def phi (s : ℕ) (p : Polynomial Coeff) : Coeff :=
  p.sum (fun r a => a * x (r + s))

def D6 : Polynomial Coeff :=
  Polynomial.C (x 1 * x 4) * Polynomial.X
    - Polynomial.C (x 1 * x 3) * Polynomial.X ^ 2
    - Polynomial.C (x 2 * x 4)
    + Polynomial.C (x 2 ^ 2) * Polynomial.X ^ 2
    + Polynomial.C (x 3 ^ 2)
    - Polynomial.C (x 2 * x 3) * Polynomial.X

def Dh (h : ℕ) : Polynomial Coeff :=
  Polynomial.C (x 1 ^ (2 * h - 8)) * D6

def weightedHomogeneous (p : Polynomial Coeff) (n : ℕ) : Prop :=
  ∀ (r : ℕ) (m : ℕ →₀ ℕ),
    MvPolynomial.coeff m (p.coeff r) ≠ 0 →
      r + m.support.sum (fun i => i * m i) = n

def zFreePart (p : Polynomial Coeff) : Coeff :=
  p.coeff 0

def claim55997 : Prop :=
  D6 ≠ 0 ∧
    phi 1 D6 = 0 ∧
    phi 2 D6 = 0 ∧
    ∀ h : ℕ, 5 ≤ h →
      weightedHomogeneous (Dh h) (2 * h - 2) ∧
      (Dh h).natDegree ≤ h - 2 ∧
      zFreePart (Dh h) =
        x 1 ^ (2 * h - 8) * (x 3 ^ 2 - x 2 * x 4) ∧
      zFreePart (Dh h) ≠ 0 ∧
      phi 1 (Dh h) = 0 ∧
      phi 2 (Dh h) = 0

end

end MarkerCycle
end MathlibPlus.Open.ResearchFormalization
