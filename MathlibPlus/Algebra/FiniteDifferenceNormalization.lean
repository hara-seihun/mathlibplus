import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim26113

open Polynomial
open scoped BigOperators

/-- `L_ell = 1 + X + ... + X^ell` from the source packet. -/
noncomputable def legPolynomial : ℕ → Polynomial ℤ
  | 0 => 1
  | ell + 1 => legPolynomial ell + X ^ (ell + 1)

/-- `R_ell = sum_{k=1}^ell (ell-k+1) X^k` from the source packet. -/
noncomputable def triangularPolynomial : ℕ → Polynomial ℤ
  | 0 => 0
  | ell + 1 => triangularPolynomial ell + X * legPolynomial ell

/-- The path-product polynomial `P_C` for a finite leg multiset. -/
noncomputable def pathProduct (C : Multiset ℕ) : Polynomial ℤ :=
  (C.map legPolynomial).prod

/-- The sum `R_C = sum_{ell in C} R_ell`. -/
noncomputable def triangularSum (C : Multiset ℕ) : Polynomial ℤ :=
  (C.map triangularPolynomial).sum

/-- The sum `G_C = sum_{ell in C} X^ell`. -/
noncomputable def endpointSum (C : Multiset ℕ) : Polynomial ℤ :=
  (C.map (fun ell => X ^ ell)).sum

/-- The `Theta_C` normalization from claim 26113. -/
noncomputable def theta (C : Multiset ℕ) : Polynomial ℤ :=
  (1 - X) * pathProduct C + X * endpointSum C

/-- The `J_C` normalization from claim 26113. -/
noncomputable def jPolynomial (C : Multiset ℕ) : Polynomial ℤ :=
  (1 - X) * pathProduct C - 1

/-- The connected-subtree polynomial in the source's double-spider formula. -/
noncomputable def connectedSubtreePolynomial
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  X ^ (c + 1) * pathProduct A * pathProduct B +
    X * legPolynomial (c - 1) * (pathProduct A + pathProduct B) +
    triangularSum A + triangularSum B + triangularPolynomial (c - 1)

/-- The numerator whose quotient by `X` is the source's normalized polynomial.
The integer casts keep the source's `n-2` and `n-1+r+s` coefficients literal. -/
noncomputable def normalizedSubtreeNumerator
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  let n : ℕ := A.sum + B.sum + c + 1
  (1 - X) ^ 2 * connectedSubtreePolynomial A B c -
      Polynomial.C ((n : ℤ) - 2) * X +
    Polynomial.C
        ((n : ℤ) - 1 + (A.card : ℤ) + (B.card : ℤ)) * X ^ 2

/-- The quotient-by-`X` normalized polynomial from the source formula. -/
noncomputable def normalizedSubtreePolynomial
    (A B : Multiset ℕ) (c : ℕ) : Polynomial ℤ :=
  normalizedSubtreeNumerator A B c /ₘ X

theorem one_sub_mul_legPolynomial (ell : ℕ) :
    (1 - X) * legPolynomial ell = 1 - X ^ (ell + 1) := by
  induction ell with
  | zero => simp [legPolynomial]
  | succ ell ih =>
      rw [legPolynomial, mul_add, ih]
      ring

/-- The finite-difference normalization of one triangular summand. -/
theorem finiteDifferenceNormalization (ell : ℕ) :
    (1 - X) ^ 2 * triangularPolynomial ell =
      Polynomial.C (ell : ℤ) * X -
        Polynomial.C ((ell + 1 : ℕ) : ℤ) * X ^ 2 + X ^ (ell + 2) := by
  induction ell with
  | zero => simp [triangularPolynomial]
  | succ ell ih =>
      rw [triangularPolynomial, mul_add, ih]
      have hleg := one_sub_mul_legPolynomial ell
      have hpow :
          (1 - X) ^ 2 * (X * legPolynomial ell) =
            X * (1 - X) * ((1 - X) * legPolynomial ell) := by
        ring
      rw [hpow, hleg]
      simp [Nat.cast_add, map_add]
      ring

/-- The summand identity lifted to a finite leg multiset. -/
theorem finiteDifferenceNormalization_sum (C : Multiset ℕ) :
    (1 - X) ^ 2 * triangularSum C =
      Polynomial.C (C.sum : ℤ) * X -
        Polynomial.C ((C.sum + C.card : ℕ) : ℤ) * X ^ 2 +
          X ^ 2 * endpointSum C := by
  induction C using Multiset.induction_on with
  | empty => simp [triangularSum, endpointSum]
  | @cons ell C ih =>
      simp only [triangularSum, endpointSum, Multiset.map_cons,
        Multiset.sum_cons, Multiset.card_cons]
      change (1 - X) ^ 2 * (triangularPolynomial ell + triangularSum C) =
        Polynomial.C ((ell + C.sum : ℕ) : ℤ) * X -
            Polynomial.C (((ell + C.sum) + (C.card + 1) : ℕ) : ℤ) * X ^ 2 +
          X ^ 2 * (X ^ ell + endpointSum C)
      rw [mul_add, finiteDifferenceNormalization ell, ih]
      simp [Nat.cast_add, map_add]
      ring

/-- The finite-difference transform and exact factorization in claim 26113.
The side multisets and the trunk length are retained as source objects; the
quotient is implemented by monic polynomial division, and the proof first
checks the corresponding numerator identity. -/
theorem normalizedSubtreeExpansion
    (A B : Multiset ℕ) (c : ℕ) (hc : 1 ≤ c) :
    normalizedSubtreePolynomial A B c =
      theta A + theta B + X ^ c * jPolynomial A * jPolynomial B := by
  have hA := finiteDifferenceNormalization_sum A
  have hB := finiteDifferenceNormalization_sum B
  have hcR := finiteDifferenceNormalization (c - 1)
  have hcL := one_sub_mul_legPolynomial (c - 1)
  have hcsub : c - 1 + 1 = c := by omega
  have hcsub2 : c - 1 + 2 = c + 1 := by omega
  have hnum :
      normalizedSubtreeNumerator A B c =
        X * (theta A + theta B + X ^ c * jPolynomial A * jPolynomial B) := by
    dsimp [normalizedSubtreeNumerator, connectedSubtreePolynomial]
    have hdist :
        (1 - X) ^ 2 *
              (X ^ (c + 1) * pathProduct A * pathProduct B +
                X * legPolynomial (c - 1) * (pathProduct A + pathProduct B) +
                triangularSum A + triangularSum B +
                triangularPolynomial (c - 1)) =
          (1 - X) ^ 2 * (X ^ (c + 1) * pathProduct A * pathProduct B) +
            (1 - X) ^ 2 * (X * legPolynomial (c - 1) *
              (pathProduct A + pathProduct B)) +
            (1 - X) ^ 2 * triangularSum A +
            (1 - X) ^ 2 * triangularSum B +
            (1 - X) ^ 2 * triangularPolynomial (c - 1) := by
      ring
    rw [hdist, hA, hB, hcR]
    have hcross :
        (1 - X) ^ 2 * (X * legPolynomial (c - 1) *
          (pathProduct A + pathProduct B)) =
          ((1 - X) ^ 2 * (X * legPolynomial (c - 1))) *
            (pathProduct A + pathProduct B) := by
      ring
    rw [hcross]
    rw [show (1 - X) ^ 2 * (X * legPolynomial (c - 1)) =
          X * (1 - X) * ((1 - X) * legPolynomial (c - 1)) by ring]
    rw [hcL]
    simp [theta, jPolynomial, hcsub, hcsub2, Nat.cast_add, map_add]
    have hcast : ((c - 1 : ℕ) : ℤ) + 1 = (c : ℤ) := by omega
    have hcastPoly :
        (c : Polynomial ℤ) = ((c - 1 : ℕ) : Polynomial ℤ) + 1 := by
      have h : (c - 1 : ℕ) + 1 = c := by omega
      rw [← h]
      simp [Nat.cast_add]
    rw [hcastPoly]
    ring
  rw [normalizedSubtreePolynomial, hnum]
  simpa using Polynomial.mul_divByMonic_cancel_left
    (theta A + theta B + X ^ c * jPolynomial A * jPolynomial B)
    Polynomial.monic_X

end MathlibPlus.Algebra.Claim26113
