import Mathlib

namespace MathlibPlus.Open.Analysis

open Polynomial

/-- The generalized-Bell polynomial recurrence from the admitted source group. -/
noncomputable def generalizedBell : Nat → Polynomial ℚ :=
  Nat.rec (2 * X - 3) (fun _ q =>
    (C (5 / 2 : ℚ) - 2 * X) * q + 2 * X * derivative q)

/-- The every-other determinant used in the normalization. -/
noncomputable def everyOtherDeterminant (r : Nat) : Polynomial ℚ :=
  Matrix.det (fun i j : Fin r => generalizedBell (2 * (i : Nat) + (j : Nat)))

/-- The normalized polynomial, obtained by dividing by the stated monomial. -/
noncomputable def normalizedPolynomial (r : Nat) : Polynomial ℚ :=
  everyOtherDeterminant r / X ^ (Nat.choose r 2)

/-- A rational polynomial has integral coefficients. -/
def HasIntegralCoefficients (p : Polynomial ℚ) : Prop :=
  ∀ k, ∃ a : ℤ, p.coeff k = (a : ℚ)

/-- Reflection of the normalized polynomial in the claim. -/
noncomputable def reflectedNormalizedPolynomial (r : Nat) : Polynomial ℚ :=
  C ((-1 : ℚ) ^ Nat.choose (r + 1) 2) *
    (normalizedPolynomial r).comp (-X)

/--
Reflected all-rank coefficient positivity: for every positive rank, the
normalized determinant polynomial has integral coefficients and its reflected
polynomial has strictly positive coefficients (in every degree up to its
natural degree), over the rationals.
-/
def reflected_all_rank_coefficient_positivity : Prop :=
  ∀ r : Nat, 1 ≤ r →
    HasIntegralCoefficients (normalizedPolynomial r) ∧
      ∀ k : Nat, k ≤ (reflectedNormalizedPolynomial r).natDegree →
        0 < (reflectedNormalizedPolynomial r).coeff k

end MathlibPlus.Open.Analysis
