import Mathlib

namespace MathlibPlus.Open.Formalization.ResidueBatch

noncomputable section

open scoped BigOperators

/-- The part of a polynomial whose degrees are strictly below `n`. -/
def truncBelow (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range n, Polynomial.C (p.coeff k) * Polynomial.X ^ k

def nodePolynomial (n : ℕ) (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (Polynomial.X - Polynomial.C (x j))

def reciprocalPolynomial (n : ℕ) (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (1 - Polynomial.C (x j) * Polynomial.X)

def vectorPolynomial (n : ℕ) (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ k : Fin n, Polynomial.C (v k) * Polynomial.X ^ (k : ℕ)

def residueNumerator (n : ℕ) (x : Fin n → ℝ) (v : Fin n → ℝ) : Polynomial ℝ :=
  truncBelow n (reciprocalPolynomial n x * vectorPolynomial n v)

def dualResidueWeight (n : ℕ) (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  1 / (w j * (Polynomial.derivative (nodePolynomial n x)).eval (x j) ^ 2)

def residueObservable (n : ℕ) (x : Fin n → ℝ) (v : Fin n → ℝ) (j : Fin n) : ℝ :=
  (x j) ^ (n - 1) * (residueNumerator n x v).eval ((x j)⁻¹)

def orderedPositiveNodes (n : ℕ) (x w : Fin n → ℝ) : Prop :=
  (∀ j, 0 < x j) ∧ (∀ j, 0 < w j) ∧
    (∀ i j : Fin n, i < j → x i < x j)

/-- Claim 7165: the vector polynomial and its truncated residue numerator. -/
def claim7165 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ) (v : Fin n → ℝ),
    orderedPositiveNodes n x w →
      vectorPolynomial n v =
          ∑ k : Fin n, Polynomial.C (v k) * Polynomial.X ^ (k : ℕ) ∧
      residueNumerator n x v =
        truncBelow n
          (reciprocalPolynomial n x *
            (∑ k : Fin n, Polynomial.C (v k) * Polynomial.X ^ (k : ℕ)))

/-- Claim 7166: dual residue weights and the observables, including positivity. -/
def claim7166 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ) (v : Fin n → ℝ),
    orderedPositiveNodes n x w →
      (∀ j : Fin n,
        dualResidueWeight n x w j =
            1 / (w j * (Polynomial.derivative (nodePolynomial n x)).eval (x j) ^ 2) ∧
        residueObservable n x v j =
            (x j) ^ (n - 1) * (residueNumerator n x v).eval ((x j)⁻¹)) ∧
      (∀ j : Fin n, 0 < dualResidueWeight n x w j)

/-- Claim 7168: the partial-fraction residue coordinates. -/
def claim7168 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ) (v : Fin n → ℝ),
    orderedPositiveNodes n x w →
      ∀ z : ℝ,
        (reciprocalPolynomial n x).eval z ≠ 0 →
          (residueNumerator n x v).eval z / (reciprocalPolynomial n x).eval z =
            ∑ j : Fin n,
              ((-(x j) * (residueNumerator n x v).eval ((x j)⁻¹)) /
                (Polynomial.derivative (reciprocalPolynomial n x)).eval ((x j)⁻¹)) /
                (1 - x j * z)

end

end MathlibPlus.Open.Formalization.ResidueBatch
