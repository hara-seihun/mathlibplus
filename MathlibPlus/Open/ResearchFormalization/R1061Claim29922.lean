import MathlibPlus.Algebra.Claim29919

namespace MathlibPlus.Open.ResearchFormalization.R1061

noncomputable section

open Polynomial

abbrev MidpointPolynomial29922 := Polynomial ℚ

def numeratorPolynomial29922
    (p q : ℕ) (δ : ℚ) : MidpointPolynomial29922 :=
  Polynomial.C ((p : ℚ) * q) * (Polynomial.X ^ p - Polynomial.X ^ q) +
    Polynomial.C δ *
      (((Polynomial.C ((p : ℚ) - q)) * Polynomial.X ^ (p + q)) -
        Polynomial.C (p : ℚ) * Polynomial.X ^ p +
        Polynomial.C (q : ℚ) * Polynomial.X ^ q)

def denominatorPolynomial29922
    (p q : ℕ) (δ : ℚ) : MidpointPolynomial29922 :=
  Polynomial.C ((p : ℚ) * q) * (Polynomial.X ^ p - Polynomial.X ^ q) +
    Polynomial.C δ *
      (Polynomial.C (p : ℚ) * Polynomial.X ^ q -
        Polynomial.C (p : ℚ) -
        Polynomial.C (q : ℚ) * Polynomial.X ^ p +
        Polynomial.C (q : ℚ))

def commonRoot29922 (p q : ℕ) (δ : ℚ) (z : ℂ) : Prop :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) z
      (numeratorPolynomial29922 p q δ) = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ ℂ) z
      (denominatorPolynomial29922 p q δ) = 0

/-- Claim 29922: in the coprime midpoint completion, the only common root is
`1`, and the common factor is simple. -/
def claim29922 : Prop :=
  ∀ (p q : ℕ) (δ : ℚ),
    0 < p → p < q → Nat.Coprime p q →
    δ ≠ 0 → δ ≠ p → δ ≠ q →
    (∀ z : ℂ, commonRoot29922 p q δ z ↔ z = 1) ∧
    gcd (numeratorPolynomial29922 p q δ)
        (denominatorPolynomial29922 p q δ) =
      Polynomial.X - Polynomial.C 1 ∧
    Polynomial.eval 1
        (Polynomial.derivative (denominatorPolynomial29922 p q δ)) =
      (p : ℚ) * q * (p - q) ∧
    (p : ℚ) * q * (p - q) ≠ 0

end
end MathlibPlus.Open.ResearchFormalization.R1061
