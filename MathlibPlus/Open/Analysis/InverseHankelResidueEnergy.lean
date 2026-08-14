import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

noncomputable section

/-- The moment sequence attached to finitely many positive nodes and weights. -/
def moment (n : ℕ) (x w : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin n, w j * (x j) ^ k

/-- The moment (Hankel) matrix. -/
def hankelMatrix (n : ℕ) (x w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => moment n x w ((a : ℕ) + (b : ℕ))

/-- The monic polynomial with the nodes as roots. -/
def nodePolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (Polynomial.X - Polynomial.C (x j))

/-- The reciprocal node polynomial. -/
def reciprocalNodePolynomial {n : ℕ} (x : Fin n → ℝ) : Polynomial ℝ :=
  ∏ j : Fin n, (Polynomial.C 1 - Polynomial.C (x j) * Polynomial.X)

/-- The polynomial consisting of the terms of degree strictly below `n`. -/
def truncateBelow (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  Finset.sum (Finset.range n) (fun k => Polynomial.C (p.coeff k) * Polynomial.X ^ k)

/-- The polynomial associated with a vector of coefficients. -/
def vectorPolynomial {n : ℕ} (v : Fin n → ℝ) : Polynomial ℝ :=
  ∑ k : Fin n, Polynomial.C (v k) * Polynomial.X ^ (k : ℕ)

/-- The truncated residue numerator. -/
def residueNumerator {n : ℕ} (x : Fin n → ℝ) (v : Fin n → ℝ) : Polynomial ℝ :=
  truncateBelow n (reciprocalNodePolynomial x * vectorPolynomial v)

/-- The dual residue weight. -/
def dualResidueWeight {n : ℕ} (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  1 / (w j * (Polynomial.eval (x j) (Polynomial.derivative (nodePolynomial x))) ^ 2)

/-- The residue observable. -/
def residueObservable {n : ℕ} (x : Fin n → ℝ) (v : Fin n → ℝ) (j : Fin n) : ℝ :=
  (x j) ^ (n - 1) * Polynomial.eval ((x j)⁻¹) (residueNumerator x v)

/-- The quadratic form `vᵀ M v`. -/
def quadraticEnergy {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ a : Fin n, v a * (M.mulVec v) a

/-- Exact inverse-Hankel residue energy. -/
def exactInverseHankelResidueEnergy : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    0 < n →
    (∀ j : Fin n, 0 < x j) →
    StrictMono x →
    (∀ j : Fin n, 0 < w j) →
    ∀ v : Fin n → ℝ,
      quadraticEnergy ((hankelMatrix n x w)⁻¹) v =
        ∑ j : Fin n, dualResidueWeight x w j * (residueObservable x v j) ^ 2

end

end MathlibPlus.Open.Analysis
