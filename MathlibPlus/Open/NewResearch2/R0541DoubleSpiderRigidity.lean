import MathlibPlus.Algebra.FiniteDifferenceNormalization

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.R0541

open MathlibPlus.Algebra.Claim26113

/-- Claim 22475: after the finite-difference normalization, the cross term is
z^c J_A J_B and the two one-sided terms are Theta_A and Theta_B. -/
def claim22475 : Prop :=
  ∀ (A B : Multiset ℕ) (c : ℕ), 1 ≤ c →
    normalizedSubtreePolynomial A B c =
      theta A + theta B + X ^ c * jPolynomial A * jPolynomial B

/-- Claim 22476: the first nonzero leg-multiplicity difference appears at the
coefficient stated for Theta. -/
def claim22476 : Prop :=
  ∀ (C C' : Multiset ℕ) (k : ℕ),
    0 < C.card → C.card = C'.card →
    (∀ j < k, C.count j = C'.count j) →
    C.count k ≠ C'.count k →
    (∀ n < k + 2, Polynomial.coeff (theta C - theta C') n = 0) ∧
      Polynomial.coeff (theta C - theta C') (k + 2) =
        -((C.card - 1 : ℕ) : ℤ) *
          ((C.count k : ℤ) - (C'.count k : ℤ))

/-- Claim 22477: with the smaller side and the larger-side leg count fixed,
equal connected-subtree polynomials force the trunk and larger side. -/
def claim22477 : Prop :=
  ∀ (A B B' : Multiset ℕ) (c c' : ℕ),
    A.sum < B.sum → A.sum < B'.sum → B.card = B'.card →
    connectedSubtreePolynomial A B c =
      connectedSubtreePolynomial A B' c' →
      c = c' ∧ B = B'

end MathlibPlus.Open.NewResearch2.R0541
