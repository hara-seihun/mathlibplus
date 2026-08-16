import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim15189

/-- The coefficient vector of a polynomial in the standard ascending monomial basis. -/
def coefficientVector (p : Polynomial ℝ) (m : ℕ) : Fin m → ℝ :=
  fun i => p.coeff i.1

/-- A monic polynomial whose natural degree is specified. -/
def monicOfDegree (p : Polynomial ℝ) (n : ℕ) : Prop :=
  p.Monic ∧ p.natDegree = n

/-- The lower-triangular Toeplitz matrix attached to a polynomial. -/
def lowerToeplitz (P : Polynomial ℝ) (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if j.1 ≤ i.1 then P.coeff (i.1 - j.1) else 0

/-- Exact Uvarov subleading-coefficient and Toeplitz-pullback formulas. -/
def exactSubleadingCoefficientFormula_claim15189 : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ (P : Polynomial ℝ) (alpha : ℝ) (v h : ℕ → ℝ)
      (π πhat q : ℕ → Polynomial ℝ),
      let lambda : ℕ → ℝ := fun k =>
        ∑ i : Fin (k + 1), v i.1 * coefficientVector (π k) (k + 1) i
      let eta : ℕ → ℝ := fun m =>
        1 + alpha * ∑ j ∈ Finset.range m, lambda j ^ 2 / h j
      P.coeff 0 ≠ 0 →
      (∀ k, k ≤ n → monicOfDegree (π k) k) →
      (∀ k, k < n → h k ≠ 0) →
      eta n ≠ 0 →
      πhat n = π n - (alpha * lambda n / eta n) •
        (∑ k ∈ Finset.range n, (lambda k / h k) • π k) →
      monicOfDegree (q n) n →
      (lowerToeplitz P (n + 1)).transpose.mulVec
          (coefficientVector (q n) (n + 1)) =
        P.coeff 0 • coefficientVector (πhat n) (n + 1) →
      (πhat n).coeff (n - 1) =
          (π n).coeff (n - 1) - alpha * lambda n * lambda (n - 1) /
            (eta n * h (n - 1)) ∧
        (q n).coeff (n - 1) =
          (π n).coeff (n - 1) - P.coeff 1 / P.coeff 0 -
            alpha * lambda n * lambda (n - 1) /
              (eta n * h (n - 1))

end MathlibPlus.Open.Analysis.Claim15189
