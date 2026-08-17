import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0823RootBlockDefiniteness

open scoped BigOperators

noncomputable section

/-- The forward finite difference of the rational coefficient polynomial. -/
def forwardDifference (P : Polynomial ℚ) : Polynomial ℚ :=
  P.comp (Polynomial.X + Polynomial.C 1) - P

/-- The parameters used by the two recurrence root blocks. -/
def ell (n r : ℕ) : ℕ := n - r - 2

def q (n r : ℕ) : ℕ := 2 * r - n + 2

def M (n : ℕ) : ℕ := n.choose 2

def N (n r : ℕ) : ℕ := M n - 2 * r

/-- The exact two-block root polynomial from the recurrence roots. -/
def rootBlockPolynomial (n r : ℕ) : Polynomial ℚ :=
  ∏ a ∈ Finset.Icc (2 * r + 1) (n + r - 2),
    (Polynomial.X - Polynomial.C (a : ℚ)) *
      (Polynomial.X -
        Polynomial.C (((M n - a - 1 : ℕ) : ℚ)))

/-- A binomial support point is in one of the two displayed root blocks. -/
def rootBlockPoint (n r j : ℕ) : Prop :=
  ∃ a ∈ Finset.Icc (2 * r + 1) (n + r - 2),
    r + j = a ∨ r + j = M n - a - 1

/-- The Record-11 Christoffel-modified binomial quadratic form. -/
def rootBlockQuadraticForm (n r : ℕ) (Q : Polynomial ℚ) : ℚ :=
  ∑ j ∈ Finset.range (N n r),
    (N n r - 1).choose j *
      Polynomial.eval (r + j : ℚ) (rootBlockPolynomial n r) *
      (Polynomial.eval (r + j : ℚ) Q) ^ 2

/-- Claim 25100: under the original primitive-wedge parameter range, the two
exact recurrence root blocks give the stated q/ell arithmetic and factor every
forward difference by the exact root-block polynomial with residual degree at
most q-1. -/
def claim25100 : Prop :=
  ∀ (n r : ℕ) (P : Polynomial ℚ),
    r + 3 ≤ n → n ≤ 2 * r → 2 * n ≥ 3 * r + 4 →
      P.natDegree ≤ n - 2 →
        q n r ≤ ell n r ∧ ell n r + q n r = r ∧
          ((∀ a ∈ Finset.Icc (2 * r + 1) (n + r - 2),
              Polynomial.eval (a : ℚ) (forwardDifference P) = 0 ∧
                Polynomial.eval ((M n - a - 1 : ℕ) : ℚ)
                  (forwardDifference P) = 0) →
            ∃ Q : Polynomial ℚ,
              forwardDifference P = rootBlockPolynomial n r * Q ∧
                Q.natDegree ≤ q n r - 1)

/-- Claim 25103: in the even-ell case, the actual root-block polynomial is
positive at every binomial support point outside its two root blocks, and its
exact Record-11 quadratic form is nonnegative and can vanish only for Q=0. -/
def claim25103 : Prop :=
  ∀ (n r : ℕ) (P Q : Polynomial ℚ),
    r + 3 ≤ n → n ≤ 2 * r → 2 * n ≥ 3 * r + 4 →
      P.natDegree ≤ n - 2 →
        Even (ell n r) →
          forwardDifference P = rootBlockPolynomial n r * Q →
            Q.natDegree ≤ q n r - 1 →
              (∀ j < N n r, ¬ rootBlockPoint n r j →
                0 < Polynomial.eval (r + j : ℚ) (rootBlockPolynomial n r)) ∧
              0 ≤ rootBlockQuadraticForm n r Q ∧
              (rootBlockQuadraticForm n r Q = 0 → Q = 0)

end

end MathlibPlus.Open.NewResearch2.R0823RootBlockDefiniteness
