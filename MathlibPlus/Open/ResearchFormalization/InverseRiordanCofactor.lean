import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

open scoped BigOperators

/-- The coefficient of the proper Riordan array in the admitted claim. -/
def riordanEntry (e t j : ℕ) : ℚ :=
  if j ≤ t then (Nat.choose (e + j) (t - j) : ℚ) else 0

/-- The polynomial whose `t`-coefficient gives the same Riordan entry. -/
def riordanGeneratingPolynomial (e j : ℕ) : Polynomial ℚ :=
  (1 + Polynomial.X) ^ e * (Polynomial.X * (1 + Polynomial.X)) ^ j

/-- The claimed inverse first-column coefficients. -/
def riordanInverseFirstColumn (e j : ℕ) : ℚ :=
  if j = 0 then 1
  else (-1 : ℚ) ^ j * (e : ℚ) / (j : ℚ) *
    (Nat.choose (e + 2 * j - 1) (j - 1) : ℚ)

/-- The determinant `D_(n,ell)^(e)` with the row set in the admitted context. -/
def riordanCofactor (e n ell : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin (ell + 1) =>
    riordanEntry e
      (if i.1 < ell then i.1 + 1 else ell + n) j.1)

/-- The inverse-Riordan cofactor formula, including the stated coefficient and
inverse-first-column descriptions. -/
def inverseRiordanCofactorFormula : Prop :=
  ∀ (d n ell : ℕ),
    1 ≤ d → 1 ≤ n → n ≤ d → ell < d →
    let e := d - ell
    (∀ t j : ℕ,
        riordanEntry e t j =
          Polynomial.coeff (riordanGeneratingPolynomial e j) t) ∧
      (∀ t : ℕ,
        (Finset.sum (Finset.range (t + 1)) (fun j =>
          riordanEntry e t j * riordanInverseFirstColumn e j)) =
          if t = 0 then 1 else 0) ∧
      riordanInverseFirstColumn e 0 = 1 ∧
      (∀ j : ℕ, 1 ≤ j →
        riordanInverseFirstColumn e j =
          (-1 : ℚ) ^ j * (e : ℚ) / (j : ℚ) *
            (Nat.choose (e + 2 * j - 1) (j - 1) : ℚ)) ∧
      riordanCofactor e n ell =
        (-1 : ℚ) ^ ell *
          Finset.sum (Finset.range (ell + 1)) (fun j =>
            riordanInverseFirstColumn e j *
              (Nat.choose (e + j) (n + ell - j) : ℚ))

end

end MathlibPlus.Open.ResearchFormalization
